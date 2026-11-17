-- Prove2me | Definitions.Def_HoneycombCodes_Supplement_HCrt
-- name    : HoneycombCodes_Supplement_HCrt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:36:11.949368+00:00
-- url     : https://prove2.me/theorems/5c6e200c-cf08-4978-91ff-d86a7dd8ee85
-- title:
--   The anchored moment relaxation $\mathrm{Mom}_{r,t}(n,d)$ and the two-axis bound $\mathrm{HC}_{r,t}(n,d)$
-- statement:
--   Let $G_{n,d}$ be the graph on $X=\{\pm1\}^n$ in which distinct $x,y$ are adjacent when $d_H(x,y)<d$; a **code** is an independent set, and $I_{\le q}$ is the set of codes of size at most $q$. For a moment sequence $y=(y_C)_{C\in I_{\le 2t}}$, extended by $0$ on non-codes, the moment matrix is $M_t(y)_{I,J}=y_{I\cup J}$ ($I,J\in I_{\le t}$), and for a quadratic polynomial $p(z)=\sum_{|A|\le2}p_Az^A$ after Boolean reduction ($z_x^2=z_x$) the localizing matrix is $M_{t-1}(py)_{I,J}=\sum_{|A|\le2}p_Ay_{I\cup J\cup A}$ ($I,J\in I_{\le t-1}$).
--
--   For every $h\in\mathfrak C_r(n)$ with $\lambda(h)>s=s_{n,d}$ put $S(z)=\sum_xz_x$, $K_h(z)=\sum_{x,y}K_h(x,y)z_xz_y$ and
--
--   $$
--   Q_h=(1-s)md_ES-(\lambda-s)K_h,\qquad T_h=K_h-d_E^2\Delta(A)S^2 .
--   $$
--
--   For $t\ge1$, the **anchored relaxation** (Definition 10.1) is
--
--   $$
--   \mathrm{Mom}_{r,t}(n,d)=\max\Big\{\sum_xy_{\{x\}}: y_\emptyset=1,\ M_t(y)\succeq0,\ M_{t-1}(Q_hy)\succeq0,\ M_{t-1}(T_hy)\succeq0\ \ (h\in\mathfrak C_r(n),\ \lambda(h)>s)\Big\},
--   $$
--
--   and the **seeded two-axis bound** (112) is $\mathrm{HC}_{r,0}(n,d)=\mathrm{HC}^{row}_r(n,d)$, $\mathrm{HC}_{r,t}(n,d)=\min\{\mathrm{HC}^{row}_r(n,d),\mathrm{Mom}_{r,t}(n,d)\}$ for $t\ge1$.
--
--   This is the anchor axis of the finite honeycomb hierarchy (Theorem 10.2).
--
--   **Formalization Note** Codes are the published `BeatingGV42.MinDistAtLeast` sets of words $\mathrm{Fin}\,n\to\mathrm{Fin}\,2$. The maximum is a real `sSup` of the feasible objective values (the maximum is attained, p.47). The localizer library ranges over every eligible certificate, possibly infinitely many.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §10, pp.46–47 (PDF 48–49), Definition 10.1 and eq. (112); eqs. (90)–(91), p.39 (PDF 41)

import Mathlib
import Definitions.Def_BeatingGV42_MinDistAtLeast
import Definitions.Def_HoneycombCodes_Supplement_HCrow

set_option autoImplicit false

namespace HoneycombCodes.Supplement

/-- A **code** of `G_{n,d}`: a set `C ⊆ {±1}ⁿ` (words `Fin n → Fin 2`) of pairwise Hamming distance
at least `d`, i.e. an independent set of the graph `G_{n,d}` whose distinct vertices are adjacent
when `d_H(x, y) < d`, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*,
arXiv:2608.20287v2 (sha256 f4b07e31…cd51), §10, p.46 (PDF 48).

**Formalization Note.** The published `BeatingGV42.MinDistAtLeast` with `q = 2`. -/
def IsCode {n : ℕ} (d : ℕ) (C : Finset (Fin n → Fin 2)) : Prop :=
  BeatingGV42.MinDistAtLeast C (d : ℝ)

open Classical in
/-- The moment functional on monomials `L_y(z_C) = y_C`, extended by `0` on non-codes (every
monomial containing a forbidden pair is mapped to zero), arXiv:2608.20287v2, §10, pp.46–47
(PDF 48–49). -/
noncomputable def momY {n : ℕ} (d : ℕ) (y : Finset (Fin n → Fin 2) → ℝ)
    (C : Finset (Fin n → Fin 2)) : ℝ :=
  if IsCode d C then y C else 0

/-- The index set `I_{≤q}` of codes of size at most `q`, arXiv:2608.20287v2, §10, p.46. -/
def CodeIdx (n d q : ℕ) : Type :=
  {I : Finset (Fin n → Fin 2) // IsCode d I ∧ I.card ≤ q}

open Classical in
noncomputable instance (n d q : ℕ) : Fintype (CodeIdx n d q) := by
  unfold CodeIdx; infer_instance

/-- The **moment matrix** `M_t(y)_{I,J} = y_{I∪J}`, `I, J ∈ I_{≤t}` (zero when `I ∪ J` is not a
code), arXiv:2608.20287v2, §10, p.47 (PDF 49). -/
noncomputable def momentMatrix {n : ℕ} (d t : ℕ) (y : Finset (Fin n → Fin 2) → ℝ) :
    Matrix (CodeIdx n d t) (CodeIdx n d t) ℝ :=
  fun I J => momY d y (I.1 ∪ J.1)

open Classical in
/-- The **localizing matrix** of order `t − 1` of the Boolean-reduced quadratic polynomial
`p(z) = Σ_{x,x′} c(x, x′) z_x z_{x′} + Σ_x ℓ(x) z_x`,
`M_{t−1}(p y)_{I,J} = Σ_{|A| ≤ 2} p_A y_{I∪J∪A}`, `I, J ∈ I_{≤t−1}`, arXiv:2608.20287v2, §10, p.47
(PDF 49).

**Formalization Note.** The Boolean reduction `z_x² = z_x` is built in: the monomial `z_x z_{x′}`
contributes `y_{I∪J∪{x, x′}}`, which is `y_{I∪J∪{x}}` when `x = x′`; monomials containing a
forbidden pair vanish through `momY`. -/
noncomputable def locMatrix {n : ℕ} (d t : ℕ) (y : Finset (Fin n → Fin 2) → ℝ)
    (c : (Fin n → Fin 2) → (Fin n → Fin 2) → ℝ) (l : (Fin n → Fin 2) → ℝ) :
    Matrix (CodeIdx n d (t - 1)) (CodeIdx n d (t - 1)) ℝ :=
  fun I J => ∑ x, ∑ x', c x x' * momY d y (I.1 ∪ J.1 ∪ {x, x'}) +
    ∑ x, l x * momY d y (I.1 ∪ J.1 ∪ {x})

/-- Feasibility for the **anchored relaxation** (Definition 10.1), arXiv:2608.20287v2, §10.1,
p.47 (PDF 49): `y_∅ = 1`, `M_t(y) ⪰ 0`, and for every certificate `h ∈ C_r(n)` with
`λ(h) > s = s_{n,d}`, `M_{t−1}(Q_h y) ⪰ 0` and `M_{t−1}(T_h y) ⪰ 0`, where (90)–(91)
`Q_h(z) = (1 − s) m d_E S(z) − (λ − s) K_h(z)`, `T_h(z) = K_h(z) − d_E² Δ(A) S(z)²`,
`S(z) = Σ_x z_x`, `K_h(z) = Σ_{x,y} K_h(x, y) z_x z_y` (p.39, PDF 41).

**Formalization Note.** `y` is defined on all finite sets of words; only its values on codes of
size at most `2t` enter (non-codes through `momY` as `0`). The localizer library is every eligible
`h ∈ C_r(n)` (possibly infinitely many). -/
def MomFeasible (r n d t : ℕ) (y : Finset (Fin n → Fin 2) → ℝ) : Prop :=
  y ∅ = 1 ∧ (momentMatrix d t y).PosSemidef ∧
    ∀ h ∈ CrLib r n, sND n d < h.lam →
      (locMatrix d t y (fun x x' => -((h.lam - sND n d) * h.K x x'))
          (fun _ => (1 - sND n d) * h.m * h.dE)).PosSemidef ∧
      (locMatrix d t y (fun x x' => h.K x x' - h.dE ^ 2 * h.Delta) (fun _ => 0)).PosSemidef

/-- The **anchored moment bound** `Mom_{r,t}(n, d) = max Σ_x y_{{x}}` over feasible `y`
(Definition 10.1), arXiv:2608.20287v2, p.47 (PDF 49), for `t ≥ 1`.

**Formalization Note.** A real `sSup` of the feasible objective values; the feasible set is nonempty
(the Dirac sequence of a code) and the objective is bounded by `2ⁿ` (`0 ≤ y_{{x}} ≤ 1`), and the
maximum is attained (p.47), so this is the printed maximum. -/
noncomputable def Mom (r n d t : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ y : Finset (Fin n → Fin 2) → ℝ, MomFeasible r n d t y ∧
    v = ∑ x, y {x}}

/-- The **seeded two-axis bound** (112), `HC_{r,0}(n, d) = HC^row_r(n, d)` and
`HC_{r,t}(n, d) = min{HC^row_r(n, d), Mom_{r,t}(n, d)}` for `t ≥ 1`, arXiv:2608.20287v2, §10.1,
p.47 (PDF 49). -/
noncomputable def HCrt (r n d t : ℕ) : ℝ :=
  if t = 0 then HCrow r n d else min (HCrow r n d) (Mom r n d t)

end HoneycombCodes.Supplement


