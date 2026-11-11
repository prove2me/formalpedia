-- Prove2me | Definitions.Def_RSVProductQLTC_ProductExpansion_locallyTestable
-- name    : RSVProductQLTC_ProductExpansion_locallyTestable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:35:52.11942+00:00
-- url     : https://prove2.me/theorems/4fe9c7a9-fa3a-40da-82b9-09453c94e208
-- title:
--   Definition 1.1 — binary locally testable code with q queries
-- statement:
--   Let $H\in\mathbb F_2^{m\times n}$ be a list of $m$ parity checks on $n$ coordinates and let $C=\ker H$. For $f\in\mathbb F_2^n$ write $\operatorname{dist}(f,C)=\min_{c\in C}|f-c|$ for its Hamming distance to $C$. For $\kappa>0$ and $q\in\mathbb N$, the code $C$ is **$\kappa$-locally testable with $q$ queries** (with respect to the checks $H$) if every check involves at most $q$ coordinates and every word at relative distance $\Delta=\operatorname{dist}(f,C)/n$ violates at least a $\kappa\Delta$ fraction of the checks:
--   $$\frac{|Hf|}{m}\ \ge\ \kappa\,\frac{\operatorname{dist}(f,C)}{n}\qquad\text{for every }f\in\mathbb F_2^n .$$
--   A CSS code is $\kappa$-locally testable with $q$ queries (Definition 1.2) when both its X-check system and its Z-check system are.
--
--   **Formalization Note.** Coordinates and checks are finite types; repeated and zero checks count towards $m$. The inequality is written without division, $\kappa\operatorname{dist}(f,C)\,m\le n\,|Hf|$; for $n,m>0$ this is the source's inequality, and for $m=0$ or $n=0$ both sides vanish. The distance is an infimum in $\mathbb N$ over the nonempty set $\ker H\ni0$, hence an attained minimum. Codewords violate no check, so they are accepted with probability $1$.
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), Definitions 1.1 and 1.2, printed p.1 (PDF p.2)

import Mathlib
set_option autoImplicit false

namespace RSVProductQLTC.ProductExpansion

/-- Hamming distance from a word `f` to the binary code `ker H` defined by the parity checks
(rows) of `H`. The minimum is over the codewords; `0 ∈ ker H`, so the index type is nonempty and
the infimum in `ℕ` is an attained minimum. -/
noncomputable def distToCode {ι κ : Type} [Fintype ι] (H : Matrix κ ι (ZMod 2))
    (f : ι → ZMod 2) : ℕ :=
  ⨅ c : {c : ι → ZMod 2 // H.mulVec c = 0}, hammingDist f c.1

/-- **Locally testable code**, Bafna–Li–Nguyen, Definition 1.1, printed p.1 (PDF p.2): for
`κ > 0` and `q ∈ ℕ`, the code `C = ker H ⊆ F₂^n` defined by the parity checks (rows) of `H` is
`κ`-locally testable with `q` queries if every check involves at most `q` coordinates and every
word `f` at relative distance `Δ = dist(f, C)/n` from `C` violates at least a `κΔ` fraction of
the checks: `|Hf| / m ≥ κ · dist(f, C) / n`, where `m` is the number of checks.

**Formalization Note.** Coordinates are a finite type `ι` (`n = |ι|`), checks a finite type `κ`
(`m = |κ|`, repeated and zero rows counted). The fraction inequality is written without division,
`κ · dist(f, C) · m ≤ n · |Hf|`; for `n, m > 0` this is the source's inequality, and for `m = 0`
or `n = 0` both sides are `0` (then `C` is the whole space). Codewords violate no check, so
"every codeword is accepted with probability 1" holds automatically. -/
def IsLocallyTestable {ι κ : Type} [Fintype ι] [Fintype κ] (kappa : ℝ) (q : ℕ)
    (H : Matrix κ ι (ZMod 2)) : Prop :=
  0 < kappa ∧ (∀ c : κ, hammingNorm (H c) ≤ q) ∧
    ∀ f : ι → ZMod 2,
      kappa * (distToCode H f : ℝ) * (Fintype.card κ : ℝ) ≤
        (Fintype.card ι : ℝ) * (hammingNorm (H.mulVec f) : ℝ)

end RSVProductQLTC.ProductExpansion


