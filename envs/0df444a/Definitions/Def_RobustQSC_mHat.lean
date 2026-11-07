-- Prove2me | Definitions.Def_RobustQSC_mHat
-- name    : RobustQSC_mHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:43.234041+00:00
-- url     : https://prove2.me/theorems/b5263131-bb5f-41bb-b2ba-2cbbce1f9e6d
-- title:
--   The operator $\hat M_{\hat f}$ and coordinate projections
-- statement:
--   For a vector $u$, let $|u_{s,i}\rangle=u(s)|s\rangle+u(s+i)|s+i\rangle$ and $M_u=\frac1{2n}\sum_{i,s}|u_{s,i}\rangle\langle u_{s,i}|/\|u_{s,i}\|_2^2$. Then
--
--   $$
--   \hat M_{\hat f}=H^{\otimes n}M_{\hat f}H^{\otimes n},\qquad\text{so that}\quad\langle g,\hat M_{\hat f}g\rangle=\mathrm{Avg}_{\hat f}[\hat g].
--   $$
--
--   For $S\subseteq\{0,1\}^n$, $\Pi_S$ is the coordinate projection onto the span of $\{|x\rangle:x\in S\}$.
--
--   **Formalization Note** A term with $u_{s,i}=0$ is $0$. The module's Lean name is `mHat f`, taking $f$ and applying the Fourier transform inside.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §7, p.55; §7.2, p.56; Theorem 9, p.55

import Definitions.Def_RobustQSC_fourier
import Definitions.Def_QAlgorithms_Defs_Information

namespace RobustQSC

open QAlgorithms

/-- The vector `|u_{s,i}⟩ = u(s)|s⟩ + u(s+i)|s+i⟩`. -/
noncomputable def edgeVec {n : ℕ} (u : EuclideanSpace ℂ (Qubits n)) (s : Qubits n) (i : Fin n) :
    EuclideanSpace ℂ (Qubits n) := by
  classical
  exact WithLp.toLp 2 fun y => if y = s then u s else if y = flip s i then u (flip s i) else 0

/-- The operator `M_u = (1/2n) Σ_{i,s} |u_{s,i}⟩⟨u_{s,i}| / ‖u_{s,i}‖²₂`, whose quadratic form
is `⟨w, M_u w⟩ = Avg_u[w]` (§4, p.21; §7.2, p.56). -/
noncomputable def mOp {n : ℕ} (u : EuclideanSpace ℂ (Qubits n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((2 * (n : ℂ))⁻¹) • ∑ i : Fin n, ∑ s : Qubits n,
    (((‖u s‖ ^ 2 + ‖u (flip s i)‖ ^ 2 : ℝ) : ℂ)⁻¹) • pureDensity (edgeVec u s i)

/-- The operator `M̂_f̂ = H^{⊗n} · (1/2n) Σ_{i,s} |u_{s,i}⟩⟨u_{s,i}| / ‖u_{s,i}‖²₂ · H^{⊗n}` with
`|u_{s,i}⟩ = f̂(s)|s⟩ + f̂(s+i)|s+i⟩`, defined so that `⟨g, M̂_f̂ g⟩ = Avg_f̂[ĝ]`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §7, p.55 ("Recall that M̂_f̂ is
defined via ⟨g, M̂_f̂ g⟩ = Avg_f̂[ĝ]"), §7.2, p.56 (display "M̂_f̂ = H^{⊗n} · 1/(2n) Σ_{i,s}
|u_{s,i}⟩⟨u_{s,i}|/‖u_{s,i}‖²₂ · H^{⊗n}").

**Formalization Note.** A term with `u_{s,i} = 0` is `0⁻¹ • 0 = 0`. -/
noncomputable def mHat {n : ℕ} (f : EuclideanSpace ℂ (Qubits n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  hadamardN n * mOp (fourier f) * hadamardN n

/-- The coordinate projection `Π_S` onto the span of `{|x⟩ : x ∈ S}` (Theorem 9, p.55). -/
noncomputable def coordProj {n : ℕ} (S : Set (Qubits n)) : Matrix (Qubits n) (Qubits n) ℂ := by
  classical
  exact Matrix.diagonal fun x => if x ∈ S then 1 else 0

/-! ### Sanity tests -/

example {n : ℕ} : coordProj (Set.univ : Set (Qubits n)) = 1 := by
  simp [coordProj, Matrix.diagonal_one]

end RobustQSC


