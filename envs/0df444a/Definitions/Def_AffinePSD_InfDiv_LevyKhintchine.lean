-- Prove2me | Definitions.Def_AffinePSD_InfDiv_LevyKhintchine
-- name    : AffinePSD_InfDiv_LevyKhintchine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:33.137814+00:00
-- url     : https://prove2.me/theorems/9fc4200f-fe34-4942-8e38-e14ce91cd4ea
-- title:
--   Functions of Lévy–Khintchine form on $S_d^+$ and the cones $\mathcal C$, $\mathcal C^S$ (§5.3)
-- statement:
--   A function $f:S_d^+\to\mathbb R$ is **of Lévy–Khintchine form on $S_d^+$** if
--   $$f(u)=\langle b_0,u\rangle-\int_{S_d^+\setminus\{0\}}\big(e^{-\langle u,\xi\rangle}-1\big)\,m_0(d\xi),\qquad u\in S_d^+,$$
--   where $b_0\in S_d^+$ and $m_0$ is a Borel measure on $S_d^+\setminus\{0\}$ with $\int(\|\xi\|\wedge1)\,m_0(d\xi)<\infty$. A distribution on $S_d^+$ is infinitely divisible iff its Laplace transform is $e^{-f}$ with $f$ of this form. Following the paper,
--   $$\mathcal C:=\{f+c\mid f\text{ of Lévy–Khintchine form on }S_d^+,\ c\in\mathbb R_+\},$$
--   $$\mathcal C^S:=\{\psi\mid u\mapsto\langle\psi(u),x\rangle\in\mathcal C\text{ for all }x\in S_d^+\}.$$
--
--   The exponents of a pure-jump affine process lie in $(\mathcal C,\mathcal C^S)$ (Proposition 5.11), which is how infinite divisibility enters Theorem 2.9.
--
--   **Formalization Note** Functions are defined on $M_d$, and only their values on $S_d^+$ are constrained. Elements of $\mathcal C^S$ map $S_d^+$ into $S_d^+$, as the compositions $\varphi(\psi)$ and $\psi_1(\psi)$ of Lemma 5.10 require. $m_0$ is a measure on $S_d^+$ with no mass at $0$, and $\|\cdot\|$ is the trace norm.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §5.3, p. 50

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone

open MeasureTheory

namespace AffinePSD.InfDiv

/-- `f` is of Lévy–Khintchine form on `S_d^+` (§5.3, p. 50):
`f(u) = ⟨b_0, u⟩ − ∫_{S_d^+ \ {0}} (e^{−⟨u,ξ⟩} − 1) m_0(dξ)` for `u ∈ S_d^+`, with `b_0 ∈ S_d^+` and a
Borel measure `m_0` on `S_d^+ \ {0}` with `∫ (‖ξ‖ ∧ 1) m_0(dξ) < ∞`.
Formalization Note: functions are on `Mat d` and only their values on `S_d^+` matter; `m_0` is a
measure on `S_d^+` with no mass at `0`. -/
def IsLK {d : ℕ} (f : AffinePSD.Necessity.Mat d → ℝ) : Prop :=
  ∃ b0 : AffinePSD.Necessity.Mat d, AffinePSD.Necessity.PSD b0 ∧ ∃ m0 : Measure (AffinePSD.Necessity.Cone d), m0 {ξ | ξ.1 = 0} = 0 ∧
    (∫⁻ ξ, ENNReal.ofReal (min (AffinePSD.Necessity.fnorm ξ.1) 1) ∂m0) < ⊤ ∧
    ∀ u, AffinePSD.Necessity.PSD u → f u = AffinePSD.Necessity.tr b0 u - ∫ ξ, (Real.exp (- AffinePSD.Necessity.tr u ξ.1) - 1) ∂m0

/-- `C := {f + c | f of Lévy–Khintchine form on S_d^+, c ∈ ℝ_+}` (§5.3, p. 50), as functions on
`S_d^+` (only values at AffinePSD.Necessity.PSD arguments matter). -/
def CC (d : ℕ) : Set (AffinePSD.Necessity.Mat d → ℝ) :=
  {φ | ∃ f c, IsLK f ∧ 0 ≤ c ∧ ∀ u, AffinePSD.Necessity.PSD u → φ u = f u + c}

/-- `C^S := {ψ | u ↦ ⟨ψ(u), x⟩ ∈ C for all x ∈ S_d^+}` (§5.3, p. 50), for maps `ψ : S_d^+ → S_d^+`.
Formalization Note: `ψ` is a function on `Mat d` mapping AffinePSD.Necessity.PSD arguments to AffinePSD.Necessity.PSD values (as the
compositions `φ(ψ)`, `ψ_1(ψ)` of Lemma 5.10 require); only its values on `S_d^+` matter. -/
def CS (d : ℕ) : Set (AffinePSD.Necessity.Mat d → AffinePSD.Necessity.Mat d) :=
  {ψ | (∀ u, AffinePSD.Necessity.PSD u → AffinePSD.Necessity.PSD (ψ u)) ∧ ∀ x, AffinePSD.Necessity.PSD x → (fun u => AffinePSD.Necessity.tr (ψ u) x) ∈ CC d}

end AffinePSD.InfDiv


