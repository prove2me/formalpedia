-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsBlindCVQC
-- name    : QiOPoQ_Supplement_IsBlindCVQC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:48:47.959086+00:00
-- url     : https://prove2.me/theorems/42fb1482-ad22-4519-a51b-c280ed7a211f
-- title:
--   Definition 3.5: blindness of a verification protocol
-- statement:
--   A protocol is blind if there is one classical PPT simulator Sim such that for every polynomial-size family $\{C_\lambda\}\in\mathcal C_{\mathsf{BQP}}$ and every non-uniform QPT distinguisher $D$,
--
--   $$\big|\Pr[D(1^\lambda,\mathsf{chall})=1:(\mathsf{chall},\mathsf{state})\leftarrow\mathrm{Gen}(1^\lambda,C_\lambda)]-\Pr[D(1^\lambda,\mathsf{chall}')=1:\mathsf{chall}'\leftarrow\mathrm{Sim}(1^\lambda,\mathrm{shape}(C_\lambda))]\big|\le\mathrm{negl}(\lambda).$$
--
--   The simulator sees only the shape, so the challenge hides the delegated circuit up to its shape.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.5, p.16

import Mathlib
import Definitions.Def_QiOPoQ_Supplement_IsCVQC
import Definitions.Def_QiOPoQ_Supplement_encShape
import Definitions.Def_QiOPoQ_UPPT

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- **Blindness (Definition 3.5).** Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289 (sha256
fe2f9210…), Definition 3.5, p.16: "Such a protocol is (computationally) blind if there is a PPT
simulator Sim such that, for every polynomial-size circuit family {C_λ}λ∈N ∈ C_BQP, for every
non-uniform QPT distinguisher D, we have that p_real(λ) := Pr[D(1^λ, chall) = 1 : (chall, state) ←
Gen(1^λ, C_λ)], p_sim(λ) := Pr[D(1^λ, chall′) = 1 : chall′ ← Sim(1^λ, shape(C_λ))], and
|p_real(λ) − p_sim(λ)| ≤ negl(λ)."

`Sim` is one classical PPT algorithm (`UPPT`), chosen before the family and the distinguisher,
run on `(1^λ, shape(C_λ))`; distinguishers are `NUQPT`. -/
def IsBlindCVQC (G : GateSet) (rad : ℕ → Circ G → List ℕ) (gen : ℕ → Circ G → List ℕ → Str × Str) :
    Prop :=
  ∃ Sim : UPPT, ∀ Cf : ℕ → Circ G, InCBQP Cf → ∀ D : NUQPT, ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n,
    |avgDice (rad n (Cf n)) (fun ω => D.acc G n (gen n (Cf n) ω).1) -
      Sim.expect (pair (unary n) (encShape (shape (Cf n)))) (fun c => D.acc G n c)| ≤ ν n

end QiOPoQ.Supplement


