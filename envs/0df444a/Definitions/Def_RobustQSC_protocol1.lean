-- Prove2me | Definitions.Def_RobustQSC_protocol1
-- name    : RobustQSC_protocol1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:54.189201+00:00
-- url     : https://prove2.me/theorems/07101a6d-adb5-4f85-aea2-1a21bbd94d41
-- title:
--   Protocol 1: one-shot two-basis robust state certification
-- statement:
--   Protocol 1, on a target $|\psi\rangle$ and a lab state $\rho$:
--
--   1. sample a basis $B\in\{X,Z\}$ with equal probability and a holdout qubit $j\in[n]$ uniformly;
--   2. measure every qubit $k\ne j$ of the lab state in basis $B$, obtaining $b\in\{0,1\}^{n-1}$;
--   3. compute a classical description of $|\psi^{(j,B)}_b\rangle$, the state left on qubit $j$ when qubits $k\ne j$ of the target are measured in basis $B$ with outcome $b$: read the two amplitudes $a_c=O_\psi((b,c),B)$, $c\in\{0,1\}$, and form $v=(a_0,a_1)$ for $B=Z$, $v=H(a_0,a_1)$ for $B=X$;
--   4. measure the holdout qubit with $\{|\psi^{(j,B)}_b\rangle\langle\psi^{(j,B)}_b|,\ 1-|\psi^{(j,B)}_b\rangle\langle\psi^{(j,B)}_b|\}$ and accept on the first outcome.
--
--   The correction by $H$ in step 3 is needed because the $\mathrm{had}$ oracle applies a Hadamard to the holdout qubit too. A run takes $n+4$ steps.
--
--   **Formalization Note** The holdout measurement uses the explicit unitary $\begin{pmatrix}a&-\bar b\\ b&\bar a\end{pmatrix}$ with $(a,b)=v/\|v\|$. If $v=0$ the observed $b$ has probability $0$ on the target, step 4 is undefined in the paper, and the protocol rejects; this event is null for a Haar-random target. Bulk qubits are measured in increasing order, which does not change the law of the outcomes. At $n=0$ there is no qubit to hold out and the protocol rejects.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Protocol 1, p.6; Definition 1, pp.7–8

import Definitions.Def_RobustQSC_AmpCertAlg

namespace RobustQSC

open QAlgorithms
open scoped ComplexConjugate

/-- The holdout vector computed from the two oracle answers `a₀ = O_ψ(b⁰, B)`,
`a₁ = O_ψ(b¹, B)` (`bᶜ` = the bulk outcome `b` with bit `j` set to `c`): `(a₀, a₁)` for the `Z`
basis (`B = std`), and `H·(a₀, a₁)` for the `X` basis (`B = had`), because the `had` oracle
returns `⟨b|H^{⊗n}|ψ⟩`, which includes a Hadamard on the holdout qubit (p.8: "This access model
allows us to explicitly and efficiently learn the leftover state on the last qubit"). -/
noncomputable def holdoutVec (had : Bool) (a₀ a₁ : ℂ) : Bool → ℂ :=
  if had then hadamard.mulVec (fun c => if c then a₁ else a₀) else fun c => if c then a₁ else a₀

/-- For `v ≠ 0`, the unitary `[[a, −b̄], [b, ā]]` with `(a, b) = v/‖v‖`, whose first column
(`U|0⟩`) is `v/‖v‖`; for `v = 0`, the identity. -/
noncomputable def unitaryOfCol (v : Bool → ℂ) : Matrix.unitaryGroup Bool ℂ := by
  classical
  exact if hv : v = 0 then 1 else
    let s : ℝ := Complex.normSq (v false) + Complex.normSq (v true)
    let r : ℂ := (Real.sqrt s : ℝ)
    let a : ℂ := v false / r
    let b : ℂ := v true / r
    ⟨Matrix.of fun i j => if j then (if i then conj a else -conj b) else (if i then b else a), by
      have hs : s ≠ 0 := by
        intro h0
        apply hv
        have h1 : Complex.normSq (v false) = 0 := by
          have := Complex.normSq_nonneg (v false); have := Complex.normSq_nonneg (v true)
          simp only [s] at h0; linarith
        have h2 : Complex.normSq (v true) = 0 := by
          have := Complex.normSq_nonneg (v false); have := Complex.normSq_nonneg (v true)
          simp only [s] at h0; linarith
        funext c; cases c
        · exact Complex.normSq_eq_zero.1 h1
        · exact Complex.normSq_eq_zero.1 h2
      have hs0 : 0 ≤ s := by
        have := Complex.normSq_nonneg (v false); have := Complex.normSq_nonneg (v true)
        simp only [s]; linarith
      have hr : Complex.normSq r = s := by
        simp only [r, Complex.normSq_ofReal]
        exact Real.mul_self_sqrt hs0
      have hab : conj a * a + conj b * b = 1 := by
        rw [mul_comm (conj a), mul_comm (conj b), Complex.mul_conj, Complex.mul_conj]
        simp only [a, b, map_div₀, hr]
        rw [← Complex.ofReal_add, ← add_div]
        rw [div_self hs, Complex.ofReal_one]
      have hab' : a * conj a + b * conj b = 1 := by rw [mul_comm a, mul_comm b]; exact hab
      clear_value a b
      rw [Matrix.mem_unitaryGroup_iff']
      ext i j
      cases i <;> cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply] <;>
        first | linear_combination hab | linear_combination hab' | ring⟩

/-- Step 2 of Protocol 1: measure the qubits of the list `qs` one after the other in the basis
`{U|0⟩, U|1⟩}`, recording outcome `o` of qubit `q` as bit `q` of `b`, then continue with `k b`. -/
noncomputable def bulkMeasure {n : ℕ} (U : Matrix.unitaryGroup Bool ℂ) :
    List (Fin n) → Qubits n → (Qubits n → AmpCertAlg n) → AmpCertAlg n
  | [], b, k => k b
  | q :: qs, b, k => AmpCertAlg.measure q U fun o => bulkMeasure U qs (Function.update b q o) k

/-- Steps 3–4 of Protocol 1 for the holdout qubit `j`, basis `had` (`false` = `Z`, `true` = `X`)
and bulk outcome `b`: query `O_ψ(b⁰, B)` and `O_ψ(b¹, B)`, form the holdout vector `v`, measure
qubit `j` in a basis whose first vector is `v/‖v‖`, and accept iff the first outcome is
obtained. If `v = 0` the protocol measures in the `Z` basis and rejects on both outcomes. -/
noncomputable def holdoutStep {n : ℕ} (j : Fin n) (had : Bool) (b : Qubits n) : AmpCertAlg n := by
  classical
  exact AmpCertAlg.query had (Function.update b j false) fun a₀ =>
    AmpCertAlg.query had (Function.update b j true) fun a₁ =>
      if holdoutVec had a₀ a₁ = 0 then
        AmpCertAlg.measure j 1 fun _ => AmpCertAlg.output false
      else
        AmpCertAlg.measure j (unitaryOfCol (holdoutVec had a₀ a₁)) fun o => AmpCertAlg.output (!o)

/-- Protocol 1 (one-shot, slightly adaptive, robust state certification):

1. sample a basis `B ∈ {X, Z}` with equal probability and a holdout qubit `j ∈ [n]` uniformly;
2. measure all qubits `k ≠ j` of the lab state in basis `B` (in increasing order), obtaining
   `b ∈ {0,1}^{n−1}`;
3. compute the classical description of the target's post-measurement state `|ψ^{(j,B)}_b⟩` on the
   holdout qubit from two oracle queries (Definition 1);
4. measure the holdout qubit with `{|ψ^{(j,B)}_b⟩⟨ψ^{(j,B)}_b|, 1 − |ψ^{(j,B)}_b⟩⟨ψ^{(j,B)}_b|}` and
   accept on the first outcome.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), Protocol 1, p.6; Definition 1,
pp.7–8.

**Formalization Note.** The basis coin is `Fin 2` (`0` = `Z`, `1` = `X`). The `Z`-basis
measurement is `U = I`, the `X`-basis one `U = H` (outcome `0` = `|+⟩`). Zero fiber: when the
target's post-measurement vector is `0` (the observed `b` has probability `0` on `|ψ⟩`, where
step 4 is undefined), the protocol rejects. At `n = 0` (no qubit to hold out) it rejects. -/
noncomputable def protocol1 (n : ℕ) : AmpCertAlg n :=
  if hn : 0 < n then
    AmpCertAlg.sample 2 (by norm_num) fun B =>
      AmpCertAlg.sample n hn fun j =>
        bulkMeasure (if B = 1 then hadamardU else 1) ((Finset.univ.erase j).sort (· ≤ ·))
          (fun _ => false) (holdoutStep j (B = 1))
  else AmpCertAlg.output false

/-! ### Sanity tests -/

/-- The holdout unitary sends `|0⟩` to `v/‖v‖`. -/
example (v : Bool → ℂ) (hv : v ≠ 0) (c : Bool) :
    (unitaryOfCol v : Matrix Bool Bool ℂ) c false =
      v c / ((Real.sqrt (Complex.normSq (v false) + Complex.normSq (v true)) : ℝ) : ℂ) := by
  cases c <;> simp [unitaryOfCol, hv]

end RobustQSC


