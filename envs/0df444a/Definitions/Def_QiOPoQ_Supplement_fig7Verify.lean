-- Prove2me | Definitions.Def_QiOPoQ_Supplement_fig7Verify
-- name    : QiOPoQ_Supplement_fig7Verify
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:53:09.804535+00:00
-- url     : https://prove2.me/theorems/d55f077a-61f0-4608-8991-9d686376ca0f
-- title:
--   Figure 7: the private verifier
-- statement:
--   Verify of Figure 7 parses the state as $(J^*,b)$ and the response as $b'\in\{0,1\}^{\mathrm{rows}\cdot\mathrm{cols}}$; it rejects ($\bot$) unless $b'_{i,j}=b_{i,j}$ at every test location $(i,j)\notin J^*$; if the bits $b'_{i,j}\oplus b_{i,j}$ at the planted locations are all equal it outputs their common value, and otherwise rejects.
--
--   **Formalization Note** A state or response that does not parse is rejected; with no planted location ($\mathrm{rows}=0$, possible only at $\lambda=0$) there is no common value and the verifier rejects.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 7, p.23

import Mathlib
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_Circ
import Definitions.Def_QiOPoQ_Supplement_encShape

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle

variable {G : GateSet}

/-- The common value of a list of bits: `some v` if the list is nonempty and every entry is `v`,
`none` otherwise. -/
def commonValue : List Bool → Option Bool
  | [] => none
  | v :: vs => if vs.all (· == v) then some v else none

open Classical in
/-- **Figure 7, Verify.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Figure 7,
p.23: "Verify(1^λ, C, chall, state, b′): Parse state = (J*, b) and
b′ = (b′_{i,j})_{i,j} ∈ {0, 1}^{rows·cols}. Check that b′_{i,j} = b_{i,j} for all test locations
(i, j) ∉ J*, and reject otherwise. If the bits b′_{i,j} ⊕ b_{i,j} for all the planted locations
(i, j) ∈ J* are all equal, output their common value; otherwise reject."

The state is parsed in the layout of `fig7Gen`; `⊥` is `none`. A state or response that does not
parse (wrong lengths, a planted location `≥ cols`) is rejected. **Formalization Note.** With
`rows = 0` there is no planted location and no common value: reject (only `λ = 0` can have
`rows = 0`). `C` and the challenge are not used. -/
noncomputable def fig7Verify (rows cols : ℕ → ℕ) (n : ℕ) (_C : Circ G) (_chall state resp : Str) :
    Option Bool :=
  let R := rows n
  let K := cols n
  match untuple state with
  | some [js, bs] =>
    match (untuple js).bind (fun l => l.mapM decNat) with
    | some J =>
      if J.length = R ∧ (∀ i ∈ J, i < K) ∧ bs.length = R * K ∧ resp.length = R * K then
        if ∀ k < R * K, J.getD (k / K) 0 ≠ k % K → resp.getD k false = bs.getD k false then
          commonValue ((List.range R).map fun i =>
            resp.getD (i * K + J.getD i 0) false ^^ bs.getD (i * K + J.getD i 0) false)
        else none
      else none
    | none => none
  | _ => none

end QiOPoQ.Supplement


