-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Proxy
-- name    : BootstrapRecolorVerify_MetricGap_Supplement_Proxy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:30:20.436219+00:00
-- url     : https://prove2.me/theorems/c80697f9-9074-4d4e-b7b9-d8e902593129
-- title:
--   Monochromatic maps, capped proxy costs and minimizing-center radius
-- statement:
--   A map $\varphi_i:V(G_i)\to V(G_i)$ is monochromatic at level $i$ when it is constant separately on each last-stage cloud. Its collapsed map reads that common color; any cloud coordinate gives the same result. For $1\le i\le r$ set
--
--   $$\overline{\operatorname{cost}}_i(\varphi_i)=\frac1{N_i}\sum_{j=1}^{i-1}\sum_{e\in E_j(G_i)}w_e\rho_{j+1}(\varphi_i(e_1),\varphi_i(e_2))+\frac1{N_iL}\sum_{u\in V(G_i)}\rho_1(u,\varphi_i(u))+B_i(\varphi_i),$$
--
--   where $B_i=0$ for $i<r$, while
--
--   $$B_r(\varphi_r)=\frac1{N_r}\sum_{e\in E_r(G_r)}w_e\,d_T(\widetilde{\varphi_r(e_1)},\widetilde{\varphi_r(e_2)}).$$
--
--   This last term vanishes on a level-$r$ monochromatic map. All edges are counted once with parallel multiplicity. No metric $\rho_{i+1}$ is used on $G_i$.
--
--   For a collapsed map $\sigma:V(G_{i-1})\to V(G_i)$ and a level-$(i-1)$ cloud $U$, a center is a vertex $a\in U$ minimizing the average of $\rho_i(\sigma(a),\sigma(b))$ over all $b\in U$. The radius $R(U)$ is this minimum. The internal-edge average divides the sum of these distances over the cloud's $3|U|/2$ unordered matching edges by that edge count. The fixed sequence used in Theorem 4.9 is
--
--   $$c_i=\frac1{2\cdot180^{i-1}i!}\quad(i\ge1).$$
--
--   These definitions contain no lower-bound or radius-estimate conclusion.
--
--   **Formalization Note** The minimum radius is a real infimum over a finite nonempty range, hence attained for the statement's $n\ge2$; the minimization predicate permits all ties. Proxy costs take extended nonnegative values on arbitrary raw histories, retaining infinite uncapped terminal distances; they coincide with the paper's finite real costs on the good event.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), §4 pp.9,12–15, Definition 4.8 and center/radius construction, p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=12; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Metrics

open scoped Classical ENNReal

namespace BootstrapRecolorVerify.MetricGap.Supplement

/-- Definition 4.8, p.12: constant separately on each last-level cloud. -/
def Monochromatic {n k : ℕ} (f : Vertex n (k + 1) → Vertex n (k + 1)) : Prop :=
  ∀ u : Vertex n k, ∀ a b : Fin (cloudSize n (k + 1)), f (u, a) = f (u, b)

/-- §4.4 p.13: choose any cloud coordinate to read its common color. For a
monochromatic input all choices give exactly the same collapsed map. -/
def collapseColoring {n k : ℕ} (f : Vertex n (k + 1) → Vertex n (k + 1))
    (a : Fin (cloudSize n (k + 1))) : Vertex n k → Vertex n (k + 1) :=
  fun u => f (u, a)

/-- The positive sequence explicitly selected in the proof, pp.13,15.
c₁=1/2, cᵢ=cᵢ₋₁/(180i) for i≥2. Its only argument is i. -/
noncomputable def lowerConstant (i : ℕ) : ℝ :=
  1 / (2 * (180 : ℝ) ^ (i - 1) * i.factorial)

/-- §4 pp.9,12: every cost is divided by Nᵢ, and the vertex term also by L.
For i<r the last-level term is absent; for i=r it is the full terminal metric.
Extended nonnegative values preserve infinity on disconnected raw histories;
on the good event these are precisely the finite real costs of the paper. -/
noncomputable def proxyCost {n i : ℕ} (r : ℕ) (H : History n i) (hi : 1 ≤ i)
    (f : Vertex n i → Vertex n i) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (Fintype.card (Vertex n i) : ℝ)) *
    ((∑ e : Edge n i,
      if h : edgeLevel e < i then
        ENNReal.ofReal (edgeWeight r n (edgeLevel e) *
          projectedRho r H (edgeLevel e + 1) (by omega)
            (f (endpoints H e).1) (f (endpoints H e).2))
      else if i = r then
        ENNReal.ofReal (edgeWeight r n (edgeLevel e)) *
          terminalDistance r H (f (endpoints H e).1) (f (endpoints H e).2)
      else 0) +
     ENNReal.ofReal ((1 / lengthScale r n) *
       ∑ u : Vertex n i, projectedRho r H 1 hi u (f u)))

/-- §4.4 p.13: average over ALL vertices of a cloud, including the center. -/
noncomputable def centerAverage {n k : ℕ} (r : ℕ) (H : History n (k + 2))
    (σ : Vertex n (k + 1) → Vertex n (k + 2)) (u : Vertex n k)
    (a : Fin (cloudSize n (k + 1))) : ℝ :=
  (1 / (cloudSize n (k + 1) : ℝ)) *
    ∑ b : Fin (cloudSize n (k + 1)), rho r H (σ (u, a)) (σ (u, b))

/-- The defining minimization criterion for any tie-breaking choice C(U).
It contains no radius bound or embedding property. -/
def IsCenter {n k : ℕ} (r : ℕ) (H : History n (k + 2))
    (σ : Vertex n (k + 1) → Vertex n (k + 2)) (u : Vertex n k)
    (a : Fin (cloudSize n (k + 1))) : Prop :=
  ∀ b, centerAverage r H σ u a ≤ centerAverage r H σ u b

/-- R(U) is the minimum of these finitely many real averages. The domain is
nonempty for every n in the statements (n≥2); no edge-average bound is built in. -/
noncomputable def centerRadius {n k : ℕ} (r : ℕ) (H : History n (k + 2))
    (σ : Vertex n (k + 1) → Vertex n (k + 2)) (u : Vertex n k) : ℝ :=
  sInf (Set.range (centerAverage r H σ u))

/-- Lemma 4.10: average over the 3n_(i−1)/2 INTERNAL UNORDERED edges,
counted once per matching label and position, retaining parallel multiplicity. -/
noncomputable def internalEdgeAverage {n k : ℕ} (r : ℕ) (H : History n (k + 2))
    (σ : Vertex n (k + 1) → Vertex n (k + 2)) (u : Vertex n k) : ℝ :=
  (1 / (Fintype.card (Fin 3 × Fin (cloudSize n (k + 1) / 2)) : ℝ)) *
    ∑ e : Fin 3 × Fin (cloudSize n (k + 1) / 2),
      rho r H (σ (u, (internalPair H.1.2.1 u e).1))
        (σ (u, (internalPair H.1.2.1 u e).2))

end BootstrapRecolorVerify.MetricGap.Supplement


