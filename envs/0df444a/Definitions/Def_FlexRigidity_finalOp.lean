-- Prove2me | Definitions.Def_FlexRigidity_finalOp
-- name    : FlexRigidity_finalOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:13.282711+00:00
-- url     : https://prove2.me/theorems/879886c3-6fa7-4847-ad72-055d07480995
-- title:
--   Input to the DD continuation (the channel $\mathcal M$ of §5.6)
-- statement:
--   For a state of the sequential protocol after $n$ rounds and a set of kept record histories: on each kept history with at least $m$ generation rounds, let $E$ be the first $m$ generation rounds; discard Alice's device memory, her records outside $E$ and the test records; Alice keeps $(x_E,a_E)$; Bob keeps his memory, the external information $R$ and his classical transcript $(u_i,y_i,b_i)_{i\le n}$. Summed over the kept histories this is the operator on $(X\times A)^m\otimes\mathbb C^d$ ($d$ = size of Bob's register) to which the DD continuation attack is applied. Histories with fewer than $m$ generation rounds contribute $0$.
--
--   **Formalization Note** With the kept set = the accepted histories this is the continuation input of Protocol 2 on $\mathrm{Acc}$; with all histories it is $\mathcal M$ applied without the acceptance check (p. 56). Bob's register is identified with $\mathbb C^d$ by a fixed enumeration.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §5.6, p. 56; Protocol 2, step 3, p. 41

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Hist
import Definitions.Def_FlexRigidity_genIdx
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The final state handed to the DD continuation, the channel `M` of §5.6** (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 56, and Protocol 2 step 3,
p. 41). For a state `ρ` of the sequential protocol after `n` rounds (records
`(c_i, u_i, x_i, y_i, a_i, b_i)`, external information `R`, memories `M^A_{n+1} M^B_{n+1}`) and a
predicate `keep` on record histories: on every kept history with at least `m` generation rounds,
`E` is the first `m` generation rounds; Alice's device memory, her records outside `E` and the
test records are discarded; Alice keeps `(x_E, a_E)`; Bob keeps his memory `M^B_{n+1}`, the
external information `R` and his classical transcript `(u_i, y_i, b_i)_{i ≤ n}` (he is also told `E`
and the decision, which are functions of what he holds on the kept histories). The result is the
operator on `(X × A)^m ⊗ ℂ^d`, with Bob's register identified with `ℂ^d`, `d = |Bob's register|`,
through `Fintype.equivFin`.

**Formalization Note** With `keep` = acceptance this is the real protocol's continuation input on
`Acc` (Protocol 2); with `keep` = everything it is `M` applied to the ideal state, which does not
condition on acceptance (p. 56). Histories with fewer than `m` generation rounds contribute `0`
(`M` outputs `0`). -/
def finalOp {X Y A B R : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [DecidableEq R]
    {n : ℕ} {dA dB : ℕ} (m : ℕ) (keep : Hist (Option Bool) (fun _ => RoundO X Y A B) n → Prop)
    [DecidablePred keep]
    (ρ : Matrix (Hist (Option Bool) (fun _ => RoundO X Y A B) n × (R × (Fin dA × Fin dB)))
      (Hist (Option Bool) (fun _ => RoundO X Y A B) n × (R × (Fin dA × Fin dB))) ℂ) :
    Matrix ((Fin m → X × A) × Fin (Fintype.card ((Fin n → Bool × Option Y × Option B) × (R × Fin dB))))
      ((Fin m → X × A) × Fin (Fintype.card ((Fin n → Bool × Option Y × Option B) × (R × Fin dB)))) ℂ :=
  let e := (Fintype.equivFin ((Fin n → Bool × Option Y × Option B) × (R × Fin dB))).symm
  ∑ h : Hist (Option Bool) (fun _ => RoundO X Y A B) n,
    let o := fun i => (Hist.ent n h i).2
    let u := fun i => (o i).1
    if hm : keep h ∧ m ≤ (genSet u).card then
      let xa : Fin m → X × A := fun j => ((o (genIdx u hm.2 j)).2.1, (o (genIdx u hm.2 j)).2.2.2.1)
      let tB : Fin n → Bool × Option Y × Option B := fun i => ((o i).1, (o i).2.2.1, (o i).2.2.2.2)
      Matrix.of fun p q =>
        if p.1 = xa ∧ q.1 = xa ∧ (e p.2).1 = tB ∧ (e q.2).1 = tB then
          ∑ ma : Fin dA, ρ (h, ((e p.2).2.1, (ma, (e p.2).2.2))) (h, ((e q.2).2.1, (ma, (e q.2).2.2)))
        else 0
    else 0

end FlexRigidity


