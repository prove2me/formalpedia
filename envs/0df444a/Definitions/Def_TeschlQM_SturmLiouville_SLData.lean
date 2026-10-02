-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_SLData
-- name    : TeschlQM_SturmLiouville_SLData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:40:24.212907+00:00
-- url     : https://prove2.me/theorems/a7082b62-6b57-4e3e-988f-899966ca7763
-- title:
--   Sturm–Liouville data: interval, coefficients and standing hypotheses (9.1)–(9.2)
-- statement:
--   Let $I = (a,b) \subseteq \mathbb{R}$ be an arbitrary open interval, with $-\infty \le a < b \le \infty$. A **Sturm–Liouville expression** on $I$ is
--   $$\tau f(x) = \frac{1}{r(x)}\Big(-\frac{d}{dx}\,p(x)\frac{d}{dx}f(x) + q(x) f(x)\Big),$$
--   where the coefficients satisfy
--
--   1. $p^{-1} \in L^1_{loc}(I)$ and $p > 0$ on $I$;
--   2. $q \in L^1_{loc}(I)$ is real-valued;
--   3. $r \in L^1_{loc}(I)$ and $r > 0$ on $I$.
--
--   The associated Hilbert space is $L^2(I, r\,dx)$ with inner product $\langle f, g\rangle = \int_a^b f(x)^* g(x) r(x)\,dx$.
--
--   These are the standing assumptions of every result of Sections 9.1–9.2; no smoothness of $p, q, r$ is assumed.
--
--   **Formalization Note.** The endpoints are extended reals (`EReal`), so infinite endpoints are allowed; $I$ is `{x : ℝ | a < x ∧ x < b}`. The weighted measure $r\,dx$ on $I$ is `(volume.restrict I).withDensity (ofReal ∘ r)`, so $L^2(I, r\,dx)$ is `Lp ℂ 2 L.measure`. `atLeft`/`atRight` are the filters $x \to a$ and $x \to b$ inside $I$. Positivity of $p$ and $r$ is required pointwise on $I$ (an $L^1_{loc}$ class that is positive a.e. has such a representative).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 181–182, Section 9.1, Eqs. (9.1)–(9.2) and hypotheses (i)–(iii)

import Mathlib

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl, Sec. 9.1, pp. 181–182: the data of a Sturm–Liouville expression
`τ f = (1/r) (−(p f′)′ + q f)` (9.1) on an arbitrary open interval `I = (a, b) ⊆ ℝ`.
The endpoints are extended reals, so `a = −∞` and `b = +∞` are allowed. The standing
requirements of p. 181 are fields of the structure:
(i) `p⁻¹ ∈ L¹_loc(I)`, `p` positive; (ii) `q ∈ L¹_loc(I)`, real-valued (`q : ℝ → ℝ`);
(iii) `r ∈ L¹_loc(I)`, `r` positive. Values of `p, q, r` outside `I` play no role. -/
structure SLData where
  /-- left endpoint `a ∈ [−∞, ∞)` -/
  a : EReal
  /-- right endpoint `b ∈ (−∞, ∞]` -/
  b : EReal
  hab : a < b
  p : ℝ → ℝ
  q : ℝ → ℝ
  r : ℝ → ℝ
  p_pos : ∀ x : ℝ, a < (x : EReal) → (x : EReal) < b → 0 < p x
  r_pos : ∀ x : ℝ, a < (x : EReal) → (x : EReal) < b → 0 < r x
  p_inv_loc : LocallyIntegrableOn (fun x => (p x)⁻¹) {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}
  q_loc : LocallyIntegrableOn q {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}
  r_loc : LocallyIntegrableOn r {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}

namespace SLData

/-- The open interval `I = (a, b)` as a subset of `ℝ`. -/
def I (L : SLData) : Set ℝ := {x : ℝ | L.a < (x : EReal) ∧ (x : EReal) < L.b}

/-- The weighted measure `r(x) dx` on `I`, so that `L²(I, r dx)` (9.2) is `Lp ℂ 2 L.measure`,
with inner product `⟨f, g⟩ = ∫_a^b f(x)* g(x) r(x) dx`. -/
noncomputable def measure (L : SLData) : Measure ℝ :=
  (volume.restrict L.I).withDensity (fun x => ENNReal.ofReal (L.r x))

/-- The filter `x → a` inside `I` (i.e. `x ↓ a` if `a` is finite, `x → −∞` if `a = −∞`). -/
noncomputable def atLeft (L : SLData) : Filter ℝ :=
  Filter.comap (fun x : ℝ => (x : EReal)) (nhdsWithin L.a (Set.Ioi L.a))

/-- The filter `x → b` inside `I` (i.e. `x ↑ b` if `b` is finite, `x → +∞` if `b = +∞`). -/
noncomputable def atRight (L : SLData) : Filter ℝ :=
  Filter.comap (fun x : ℝ => (x : EReal)) (nhdsWithin L.b (Set.Iio L.b))

end SLData

end TeschlQM.SturmLiouville


