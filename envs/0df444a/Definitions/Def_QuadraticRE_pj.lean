-- Prove2me | Definitions.Def_QuadraticRE_pj
-- name    : QuadraticRE_pj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:11:50.198212+00:00
-- url     : https://prove2.me/theorems/67f28659-9f41-4d15-aff2-bedb1482a0f9
-- title:
--   The reconstruction probabilities $p_j$, $q_j(c)$, $q^*_j$ (8)
-- statement:
--   Let $\tilde y$ be uniform on $\mathbb F_2^L$ and, independently, $\mathbf c=\mathrm{Sh}^j_C(c;\theta_C)$ with uniform masks. Then
--   $$p_j=\Pr\bigl[\mathrm{Auth}^j_C(\{i:\tilde y_i=0\})\bigr],\quad q_j(c)=\Pr\bigl[\mathrm{Auth}^j_A(\{i:\tilde y_i=0,\ c_i=1\})\bigr],\quad q^*_j=\max\{q_j(0),q_j(1)\}.$$
--   $p_j$ has no secret argument: whether a set is authorized does not depend on the root value. Also $\beta(x)=1-(1-x)^2$.
--
--   These are the two probabilities that bound the privacy error of $E_{j,h}$.
--
--   **Formalization Note** Both are counts over the uniform choices, never recurrences: the recurrences are Lemma 4.9. $p_j$ is a count over $\tilde y$ only, $q_j(c)$ over $(\tilde y,\theta_C)$.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), eq. (8), p.23; Lemma 4.9, p.27

import Mathlib
import Definitions.Def_QuadraticRE_Auth

namespace QuadraticRE

/-- `p_j = Pr[Auth^j_C({i : ỹ_i = 0}) = 1]`, (8) of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.23, for `ỹ` uniform on `F₂^L`.
It has no secret argument: "The selection depends only on `ỹ`, and whether the set is authorized does
not depend on the root value".

**Formalization Note.** A count over `ỹ`, never a recurrence: (11) is Lemma 4.9. -/
noncomputable def pj (j : ℕ) : ℝ :=
  prob (fun yt : Fin (4 ^ j) → F2 => Auth .C j (Finset.univ.filter (fun i => yt i = 0)))

/-- `q_j(c) = Pr[Auth^j_A({i : ỹ_i = 0, c_i = 1}) = 1]`, (8), p.23, for `ỹ` uniform on `F₂^L` and,
independently, `c = Sh^j_C(c; θ_C)` with uniform masks.

**Formalization Note.** A count over `(ỹ, θ_C)`, never a recurrence: (12), (13) are Lemma 4.9. -/
noncomputable def qj (j : ℕ) (c : F2) : ℝ :=
  prob (fun ω : (Fin (4 ^ j) → F2) × (Fin (maskLen .C j) → F2) =>
    Auth .A j (Finset.univ.filter (fun i => ω.1 i = 0 ∧ Sh .C j c ω.2 i = 1)))

/-- `q*_j = max{q_j(0), q_j(1)}`, (8), p.23. -/
noncomputable def qStar (j : ℕ) : ℝ := max (qj j 0) (qj j 1)

/-- `β(x) = 1 − (1 − x)² = 2x − x²`, Lemma 4.9, p.27. -/
def beta (x : ℝ) : ℝ := 1 - (1 - x) ^ 2

end QuadraticRE


