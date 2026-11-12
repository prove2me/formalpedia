-- Prove2me | Definitions.Def_QubitTracking_rhoReprog31
-- name    : QubitTracking_rhoReprog31
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:32:07.640198+00:00
-- url     : https://prove2.me/theorems/6af455c0-f67a-423e-9a26-70246644c4fc
-- title:
--   Lemma 3.1's experiments: one broadcast per verifier, real and reprogrammed random oracle
-- statement:
--   In the one-round schedule, $\mathcal V_L$ broadcasts a uniform $x_l\in\mathbb F_2^\lambda$ at time $t_l$ and $\mathcal V_R$ a uniform $x_r$ at time $t_r$; a prover (no input, no responses) has query access to a uniformly random oracle $H=\mathcal O_{\mathsf{random}}:\mathbb F_2^\lambda\to\mathbb F_2^m$. In the **real experiment** every query is answered by $H$. In the **reprogrammed experiment** a query located at a spacetime point $(p,t)$ with
--   $$t-t_l\ge p+1\quad\text{and}\quad t-t_r\ge 1-p$$
--   is answered by $H$ reprogrammed to a uniform $y$ at $x_l\oplus x_r$. The outputs are the final states of all the prover's cells, averaged over all randomness.
--
--   These are the two cases compared in Lemma 3.1.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 3.1, p.23

import Definitions.Def_QubitTracking_Prover

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-! The two experiments of Lemma 3.1 ([Unr14]): one broadcast by each verifier, a random oracle,
and its reprogramming inside the intersection of the two future light cones.

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 3.1, p.23. -/

/-- The one-round schedule of Lemma 3.1: `𝒱_L` broadcasts at time `t_l`, `𝒱_R` at time `t_r`; there
are no responses (the deadlines are unused). -/
def sched31 (tl tr : ℝ) : Sched where
  N := 0
  sendL _ := tl
  sendR _ := tr
  deadL _ := tl
  deadR _ := tr

/-- A prover for Lemma 3.1: no input register, challenges of `λ` bits, no responses, one oracle
`𝒪_random : 𝔽₂^λ → 𝔽₂^m`. -/
abbrev Prover31 (lam m : ℕ) (tl tr : ℝ) : Type 1 :=
  Prover (sched31 tl tr) lam 0 0 Unit (fun _ => lam) (fun _ => m)

/-- The reprogramming region of Lemma 3.1: the spacetime points `(p, t)` with `t − t_l ≥ p + 1`
and `t − t_r ≥ 1 − p`. -/
def InReprogRegion (tl tr p t : ℝ) : Prop := p + 1 ≤ t - tl ∧ 1 - p ≤ t - tr

open Classical in
/-- The initial state: the challenge cells hold `x_l` and `x_r`, every other cell `|0⟩`. -/
noncomputable def init31 {lam m : ℕ} {tl tr : ℝ} (P : Prover31 lam m tl tr)
    (xl xr : Bits (Fin lam)) : Bits (Fin 0 ⊕ P.Cell) → ℂ :=
  fun f =>
    if (∀ j, f (Sum.inr (P.chalL 0 j)) = xl j) ∧ (∀ j, f (Sum.inr (P.chalR 0 j)) = xr j) ∧
        (∀ c, (∀ j, P.chalL 0 j ≠ c) → (∀ j, P.chalR 0 j ≠ c) → f (Sum.inr c) = 0)
    then 1 else 0

/-- **The real experiment of Lemma 3.1**: `𝒱_L` broadcasts a uniform `x_l` at `t_l`, `𝒱_R` a
uniform `x_r` at `t_r`, and every query is answered by the uniformly random oracle
`𝒪_random = H`. The result is the final state of all the prover's cells, averaged over
`(H, x_l, x_r)`. -/
noncomputable def rhoReal31 {lam m : ℕ} {tl tr : ℝ} (P : Prover31 lam m tl tr) :
    Matrix (Bits (Fin 0 ⊕ P.Cell)) (Bits (Fin 0 ⊕ P.Cell)) ℂ :=
  avgMat fun ω : (Bits (Fin lam) → Bits (Fin m)) × Bits (Fin lam) × Bits (Fin lam) =>
    proj (P.finalState (Fin 0) (fun _ _ _ => ω.1) (init31 P ω.2.1 ω.2.2))

open Classical in
/-- **The reprogrammed experiment of Lemma 3.1**: as the real one, but `𝒪_random` is reprogrammed
to a uniformly random output `y` on input `x_l ⊕ x_r` for every query located at a spacetime
point `(p, t)` of the region `t − t_l ≥ p + 1`, `t − t_r ≥ 1 − p`. Averaged over
`(H, x_l, x_r, y)`. -/
noncomputable def rhoReprog31 {lam m : ℕ} {tl tr : ℝ} (P : Prover31 lam m tl tr) :
    Matrix (Bits (Fin 0 ⊕ P.Cell)) (Bits (Fin 0 ⊕ P.Cell)) ℂ :=
  avgMat fun ω : (Bits (Fin lam) → Bits (Fin m)) × Bits (Fin lam) × Bits (Fin lam) × Bits (Fin m) =>
    proj (P.finalState (Fin 0)
      (fun p t _ q => if InReprogRegion tl tr p t ∧ q = ω.2.1 + ω.2.2.1 then ω.2.2.2 else ω.1 q)
      (init31 P ω.2.1 ω.2.2.1))

end QubitTracking


