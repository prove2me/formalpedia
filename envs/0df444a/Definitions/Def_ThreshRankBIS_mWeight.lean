-- Prove2me | Definitions.Def_ThreshRankBIS_mWeight
-- name    : ThreshRankBIS_mWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:01:52.753262+00:00
-- url     : https://prove2.me/theorems/0435e54d-b2eb-4196-8561-a8cbba0f1f0d
-- title:
--   Class weight $m_\lambda(w,t)$, tail $Z_{\ge T}$ and the cutoff $T$ of (17)
-- statement:
--   Let $q=1+\lambda$. For integers $w,t\ge0$ define the class
--
--   $$
--   H(w,t)=\{B\subseteq X:\ |N(B)|=w,\ |[B]|=w-t\},\qquad m_\lambda(w,t)=q^{-w}\sum_{B\in H(w,t)}\lambda^{|B|},
--   $$
--
--   so $m_\lambda(w,t)$ is the contribution of this class to $Z_G(\lambda)/q^n$. The **high-deficit tail** is
--
--   $$
--   Z_{\ge T}=\sum_{J\in\mathcal I(G),\ t(J\cap X)\ge T}\lambda^{|J|},
--   $$
--
--   and, for constants $a,c>0$, a list size $K$ and $0<\epsilon\le1$, the **cutoff** (17) is
--
--   $$
--   T=\min\Bigl\{n+1,\Bigl\lceil\frac{v_d+\log(4K(n+1)^2/\epsilon)}{c}\Bigr\rceil\Bigr\},\qquad v_d=3ne^{-ad}.
--   $$
--
--   The tail is what the covered family omits (Lemma 8), and the cutoff is the value of $T$ at which the container bound makes it at most $(\epsilon/4)Z_G(\lambda)$ (Corollary 12).
--
--   **Formalization Note** $w-t$ is an integer, so $H(w,t)=\emptyset$ when $w<t$; $T$ is an integer (the ceiling of a real number).
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), §4, p.12; §3.3, p.11; Corollary 12, display (17), p.15

import Mathlib
import Definitions.Def_ThreshRankBIS_closure
import Definitions.Def_ThreshRankBIS_hardcoreZ
set_option autoImplicit false

namespace ThreshRankBIS

open Finset

/-- The class `H(w, t) = {B ⊆ X : |N(B)| = w, |[B]| = w − t}` (§4, p.12).

**Formalization Note.** `w − t` is an integer: for `w < t` the class is empty, as in the paper
(a truncated natural-number difference would wrongly admit `B = ∅` at `w = 0`). -/
def Hwt {n : ℕ} (E : Fin n → Fin n → Bool) (w t : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter (fun B => (#(nbhd E B) : ℤ) = w ∧ (#(closure E B) : ℤ) = (w : ℤ) - t)

/-- **The normalized class weight** `m_λ(w, t) = q^{−w} ∑_{B ∈ H(w,t)} λ^{|B|}`, `q = 1 + λ`
(§4, p.12): the contribution of the class `H(w, t)` to `Z_G(λ)/q^n`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), §4, p.12; §3.3,
p.11 (`Z_{≥T}`); Corollary 12, display (17), p.15 (the cutoff `T`).

The module also defines the class `H(w, t)`, the high-deficit tail
`Z_{≥T} = ∑_{J ∈ 𝓘(G), t(J ∩ X) ≥ T} λ^{|J|}` (p.11) and the cutoff
`T = min{n + 1, ⌈(v_d + log(4K(n+1)²/ε))/c⌉}` of (17), `v_d = 3ne^{−ad}`. -/
noncomputable def mWeight {n : ℕ} (E : Fin n → Fin n → Bool) (lam : ℝ) (w t : ℕ) : ℝ :=
  ((1 + lam) ^ w)⁻¹ * ∑ B ∈ Hwt E w t, lam ^ #B

/-- The high-deficit tail `Z_{≥T} = ∑_{J ∈ 𝓘(G), t(J ∩ X) ≥ T} λ^{|J|}` (§3.3, p.11). -/
noncomputable def Ztail {n : ℕ} (E : Fin n → Fin n → Bool) (T : ℤ) (lam : ℝ) : ℝ := by
  classical
  exact ∑ J ∈ univ.filter (fun J : Finset (V n) => IsIndep E J ∧ T ≤ deficit E (leftPart J)),
    lam ^ #J

/-- The cutoff (17) (p.15): `T = min{n + 1, ⌈(v_d + log(4K(n + 1)²/ε))/c⌉}` with
`v_d = 3ne^{−ad}`, as an integer. -/
noncomputable def cutoffT (n d K : ℕ) (a c ε : ℝ) : ℤ :=
  min ((n : ℤ) + 1)
    ⌈(3 * (n : ℝ) * Real.exp (-(a * d)) + Real.log (4 * K * ((n : ℝ) + 1) ^ 2 / ε)) / c⌉

end ThreshRankBIS


