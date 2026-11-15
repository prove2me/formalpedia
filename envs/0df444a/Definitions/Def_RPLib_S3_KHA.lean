-- Prove2me | Definitions.Def_RPLib_S3_KHA
-- name    : RPLib_S3_KHA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:33:57.018809+00:00
-- url     : https://prove2.me/theorems/cba82627-9416-4f2d-9045-0afe84972dd4
-- title:
--   Kronecker-Hurwitz class number relation: Popa-Zagier weights and the local (cone) identity
-- statement:
--   Popa-Zagier weights and the local (cone) identity.
--
--   A matrix `N = (P Q; R S)` is stored as `(P, Q, R, S)`; its form is `[A, B, C] = [R, S - P, -Q]`.
--   * `hs u` = `1, 1/2, 0` for `u > 0, u = 0, u < 0`; `cor u v` = `[u = 0 ∧ v = 0]`;
--   * `wt A B C` : weight of the closed half domain `0 ≤ B ≤ A ≤ C` (`1` inside, `1/2` on an edge, `1/4` at `i`,
--     `1/6` at `ρ²`); `kp A B C` : weight of the cone `B ≤ A ≤ C` (`1/6` at the vertex);
--   * **`local_id`** : for `R, S > 0`, `kp(N) = wt(N) + wt(N S) + kp(N T) + kp(N T')` with
--     `S = (0 -1; 1 0)`, `T = (1 1; 0 1)`, `T' = (1 0; 1 1)` (Popa-Zagier, arXiv 1604.02822, cone decomposition).
--
--   **Formalization note.** Library module of an elementary formalization of the Kronecker-Hurwitz class number relation $\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \sum_{d \mid n} \min(d, n/d)$ (Popa-Zagier's tessellation proof, recast as a telescoping identity over integer matrices of determinant $n$), part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. A. Popa and D. Zagier, A combinatorial refinement of the Kronecker-Hurwitz class number relation, arXiv:1604.02822 (2016); L. Kronecker, Über die Anzahl der verschiedenen Classen quadratischer Formen von negativer Determinante, J. reine angew. Math. 57 (1860), 248-255; A. Hurwitz, Über Relationen zwischen Classenanzahlen binärer quadratischer Formen von negativer Determinante, Math. Ann. 25 (1885), 157-196; H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3

import Mathlib

/-!
# S3-KH, part A: Popa-Zagier weights and the local (cone) identity

A matrix `N = (P Q; R S)` is stored as `(P, Q, R, S)`; its form is `[A, B, C] = [R, S - P, -Q]`.
* `hs u` = `1, 1/2, 0` for `u > 0, u = 0, u < 0`; `cor u v` = `[u = 0 ∧ v = 0]`;
* `wt A B C` : weight of the closed half domain `0 ≤ B ≤ A ≤ C` (`1` inside, `1/2` on an edge, `1/4` at `i`,
  `1/6` at `ρ²`); `kp A B C` : weight of the cone `B ≤ A ≤ C` (`1/6` at the vertex);
* **`local_id`** : for `R, S > 0`, `kp(N) = wt(N) + wt(N S) + kp(N T) + kp(N T')` with
  `S = (0 -1; 1 0)`, `T = (1 1; 0 1)`, `T' = (1 0; 1 1)` (Popa-Zagier, arXiv 1604.02822, cone decomposition).
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.KH

/-- Half step: `1`, `1/2`, `0` for `u > 0`, `u = 0`, `u < 0`. -/
def hs (u : ℤ) : ℚ := if 0 < u then 1 else if u = 0 then 1 / 2 else 0

/-- Corner indicator `[u = 0 ∧ v = 0]`. -/
def cor (u v : ℤ) : ℚ := if u = 0 ∧ v = 0 then 1 else 0

/-- Weight of a form `[A, B, C]` in the closed half fundamental domain `0 ≤ B ≤ A ≤ C`. -/
def wt (A B C : ℤ) : ℚ := hs B * hs (A - B) * hs (C - A) - cor (A - B) (C - A) / 12

/-- Weight of a form `[A, B, C]` in the cone `B ≤ A ≤ C`. -/
def kp (A B C : ℤ) : ℚ := hs (A - B) * hs (C - A) - cor (A - B) (C - A) / 12

lemma hs_pos {u : ℤ} (h : 0 < u) : hs u = 1 := by simp [hs, h]
lemma hs_zero {u : ℤ} (h : u = 0) : hs u = 1 / 2 := by simp [hs, h]
lemma hs_neg {u : ℤ} (h : u < 0) : hs u = 0 := by
  simp [hs, not_lt.2 h.le, h.ne]
lemma cor_one {u v : ℤ} (h1 : u = 0) (h2 : v = 0) : cor u v = 1 := by simp [cor, h1, h2]
lemma cor_l {u v : ℤ} (h : u ≠ 0) : cor u v = 0 := by simp [cor, h]
lemma cor_r {u v : ℤ} (h : v ≠ 0) : cor u v = 0 := by simp [cor, h]

/-- Matrix weight `wt` of the form of `N`. -/
def wN (N : ℤ × ℤ × ℤ × ℤ) : ℚ := wt N.2.2.1 (N.2.2.2 - N.1) (-N.2.1)

/-- Matrix cone weight. -/
def kN (N : ℤ × ℤ × ℤ × ℤ) : ℚ := kp N.2.2.1 (N.2.2.2 - N.1) (-N.2.1)

/-- `N ↦ N S`, `S = (0 -1; 1 0)`. -/
def mS (N : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (N.2.1, -N.1, N.2.2.2, -N.2.2.1)

/-- `N ↦ N T`, `T = (1 1; 0 1)`. -/
def mT (N : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (N.1, N.1 + N.2.1, N.2.2.1, N.2.2.1 + N.2.2.2)

/-- `N ↦ N T'`, `T' = (1 0; 1 1)`. -/
def mT' (N : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (N.1 + N.2.1, N.2.1, N.2.2.1 + N.2.2.2, N.2.2.2)

/-- The determinant `P S - Q R`. -/
def det4 (N : ℤ × ℤ × ℤ × ℤ) : ℤ := N.1 * N.2.2.2 - N.2.1 * N.2.2.1

/-- **Local identity** (cone decomposition). -/
theorem local_id (P Q R S : ℤ) (hR : 0 < R) (hS : 0 < S) :
    kN (P, Q, R, S) = wN (P, Q, R, S) + wN (mS (P, Q, R, S)) + kN (mT (P, Q, R, S)) +
      kN (mT' (P, Q, R, S)) := by
  simp only [kN, wN, mS, mT, mT', kp, wt]
  rcases lt_trichotomy P S with h1 | h1 | h1 <;>
  rcases lt_trichotomy (-Q) R with h2 | h2 | h2 <;>
  rcases lt_trichotomy (-Q) (R + S) with h3 | h3 | h3 <;>
  rcases lt_trichotomy (S - P - Q) (R + S) with h4 | h4 | h4 <;>
  rcases lt_trichotomy (S - P) R with h5 | h5 | h5 <;>
  first
  | omega
  | (simp (disch := omega) only [hs_pos, hs_zero, hs_neg, cor_one, cor_l, cor_r]; norm_num)

end RamanujanPetersson.S3.KH


