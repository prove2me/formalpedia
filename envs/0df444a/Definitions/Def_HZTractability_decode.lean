-- Prove2me | Definitions.Def_HZTractability_decode
-- name    : HZTractability_decode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:14:35.121373+00:00
-- url     : https://prove2.me/theorems/79edbc1e-d7f3-4113-b983-8c3e921d2d82
-- title:
--   Group minimum prices, equalized prices and the decoder (display (4))
-- statement:
--   For prices $p$ of $M(G;a,\tau,K)$ write
--   $$
--   q_v=\min_{j\in L_v}p_j,\quad m_v=\min_{j\in M_v}p_j,\quad p_v=\min_{j\in H_v}p_j,\quad r_{Fv}=\min_{j\in RF_v}p_j,\quad r_{Uv}=\min_{j\in RU_v}p_j .
--   $$
--   Prices are **equalized** if they are constant on every group (each of the five groups at each vertex, and $Z$). The **decoder** maps prices to the threshold vector
--   $$
--   t_v=\frac{p_v-L}{w},\qquad z_v=\mathrm{clip}(t_v),\qquad \mathrm{clip}(t)=\min\{1,\max\{0,t\}\}.
--   $$
--
--   The decoder depends only on group minima, so it is unchanged by the equalization of Lemma 2.3.
--
--   **Formalization Note** The minimum of a group is the infimum of its finitely many prices; every group is nonempty for admissible $K$ (Lemma A.1).
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §3.2, display (4), p.11 (PDF p.13); clip, p.6

import Mathlib
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_Market

namespace HZTractability

/-- The minimum price of the group `g` at vertex `v` (§3.2, p.11 (PDF 13)): `q_v`, `m_v`, `p_v`,
`r_{Fv}`, `r_{Uv}` for `g = L, M, H, RF, RU` ("q_v = min_{j∈L_v} p_j, …").

**Formalization Note** The minimum of a finite set is its `sInf`; every group is nonempty for
admissible `K` (Lemma A.1), and the value `0` of an empty `sInf` never enters. -/
noncomputable def grpMin {a τ : ℚ} {K : ℕ} {G : ThrGraph} (p : Good a τ K G → ℝ)
    (v : Fin G.n) (g : GTag) : ℝ :=
  sInf (Set.range fun k : Fin (supCount a τ K (G.outdeg v) g) => p (Sum.inl ⟨v, g, k⟩))

/-- **Equalized group prices** (§3.2, p.11; §4.5, p.17; App. B, p.38: "equalize prices within each
group using Lemma 2.3"): the price is constant on every group of `M(G; a, τ, K)`, i.e. on each of
the five groups at every vertex and on the balancing group `Z`. -/
def IsGroupEqualized {a τ : ℚ} {K : ℕ} {G : ThrGraph} (p : Good a τ K G → ℝ) : Prop :=
  (∀ (v : Fin G.n) (g : GTag) (k k' : Fin (supCount a τ K (G.outdeg v) g)),
      p (Sum.inl ⟨v, g, k⟩) = p (Sum.inl ⟨v, g, k'⟩)) ∧
    ∀ k k' : Fin (Fintype.card (Buyer a τ K G) - Glisted a τ K G), p (Sum.inr k) = p (Sum.inr k')

/-- `clip(t) = min{1, max{0, t}}` (§1, p.6 (PDF 8)). -/
def clip (t : ℝ) : ℝ := min 1 (max 0 t)

/-- **The decoder** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held version, sha256
74b7bf9f…, display (4), p.11 (PDF 13)): "t_v = (p_v − L)/w, z_v = clip(t_v)", where `p_v` is the
minimum price of the high group `H_v` and `L`, `w` are from (8).

**Formalization Note** `decode` uses the group minimum, so it applies to every price vector,
equalized or not (§3.2, p.11: "the decoder depends only on the group minima"). -/
noncomputable def decode {a τ : ℚ} {K : ℕ} {G : ThrGraph} (p : Good a τ K G → ℝ)
    (v : Fin G.n) : ℝ :=
  clip ((grpMin p v GTag.H - (Lp a K : ℝ)) / (wp a K : ℝ))

end HZTractability


