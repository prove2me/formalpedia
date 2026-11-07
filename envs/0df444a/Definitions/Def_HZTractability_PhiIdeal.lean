-- Prove2me | Definitions.Def_HZTractability_PhiIdeal
-- name    : HZTractability_PhiIdeal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:18:46.226568+00:00
-- url     : https://prove2.me/theorems/9fefd40a-becd-41fb-bfba-dcbd16494bf4
-- title:
--   Ideal wire payments $I_{uv}$, the residual $\Phi_v(p)$, and the expenditures $W_v$, $V_v$
-- statement:
--   For high prices $p_u$, $p_v$ the ideal payment of the $K$ wire buyers of $u\to v$ to $H_v$ is
--   $$
--   I_{uv}=\frac{K\,p_v(1-a^2p_u)}{p_v-a^2p_u}.
--   $$
--   Evaluated at the ideal low and middle prices $a^2p_v$, $ap_v$, the target revenue is $R_v=p_v(a^2S_L+aS_M+S_H)$, the wire receipts are $E_v=\sum_{v\to t}(K-I_{vt})+\sum_{u\to v}I_{uv}$, and the **residual** is
--   $$
--   \Phi_v(p)=R_v-E_v-b_v-c_v .
--   $$
--   $W_v$ and $V_v$ denote the actual approved expenditures of the floor buyers and of the upper buyers at $v$ on the three targets $L_v$, $M_v$, $H_v$.
--
--   Lemma B.5 compares $\Phi_v$ with $W_v+(V_v-c_v)$ and with the incoming sum of the threshold game.
--
--   **Formalization Note** $p_u$ is the minimum price of $H_u$; the counts are the natural-number counts of the market at $v$. A self-loop appears once in each sum of $E_v$. The denominators are positive wherever Lemma B.5 is applied.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), displays (13), (15), (16), pp.15–16 (PDF pp.17–18); Lemma B.5, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_Market
import Definitions.Def_HZTractability_decode

namespace HZTractability

/-- **The ideal wire payment** `I_uv` (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held
version, sha256 74b7bf9f…, display (13), p.15 (PDF 17)): "I_uv = K p_v (1 − a² p_u)/(p_v − a² p_u)",
the total spending of the `K` wire buyers of `u → v` on `H_v` when the low price at `u` is
`a² p_u`; here `pu`, `pv` are the high prices at `u` and `v`.

**Formalization Note** Real division; the denominator is positive in every use (Lemma B.4 puts the
high prices near `[L, U]` with `L > 1 > a² p_u`). -/
noncomputable def Iwire (a : ℚ) (K : ℕ) (pu pv : ℝ) : ℝ :=
  (K : ℝ) * pv * (1 - (a : ℝ) ^ 2 * pu) / (pv - (a : ℝ) ^ 2 * pu)

/-- **The ideal residual** `Φ_v(p)` (arXiv:2610.35848, (15), (16), p.16 (PDF 18), as evaluated in
Lemma B.5, p.42 (PDF 44): "evaluate the rational wire payments (13) and residual (16) at the ideal
low and middle prices a²p_u, ap_u, keeping the actual high prices p_u").

With `p_u` the high price at `u` (`grpMin p u H`):
`Φ_v(p) = R_v − E_v − b_v − c_v`, where `R_v = a²p_v S_L + a p_v S_M + p_v S_H` is the ideal target
revenue and `E_v = ∑_{v→t} (K − I_vt) + ∑_{u→v} I_uv` the ideal wire receipts.

**Formalization Note** `S_L`, `S_M`, `S_H`, `b_v`, `c_v` are the natural-number counts of the
market at `v`. A self-loop `v → v` appears once in each of the two sums of `E_v`. -/
noncomputable def PhiIdeal {a τ : ℚ} {K : ℕ} {G : ThrGraph} (p : Good a τ K G → ℝ)
    (v : Fin G.n) : ℝ :=
  let P : Fin G.n → ℝ := fun u => grpMin p u GTag.H
  let o := G.outdeg v
  ((a : ℝ) ^ 2 * P v * (supCount a τ K o GTag.L : ℝ) + (a : ℝ) * P v * (supCount a τ K o GTag.M : ℝ)
      + P v * (supCount a τ K o GTag.H : ℝ))
    - ((∑ t ∈ Finset.univ.filter (fun t => G.adj v t = true), ((K : ℝ) - Iwire a K (P v) (P t)))
      + ∑ u ∈ Finset.univ.filter (fun u => G.adj u v = true), Iwire a K (P u) (P v))
    - (popCount a τ K (G.indeg v) o BTag.BLM : ℝ) - (popCount a τ K (G.indeg v) o BTag.BMH : ℝ)

/-- `j` is a target good of `v`: a good of `L_v`, `M_v` or `H_v`. -/
abbrev IsTargetOf {a τ : ℚ} {K : ℕ} {G : ThrGraph} (v : Fin G.n) (j : Good a τ K G) : Prop :=
  goodInfo j = some (v, GTag.L) ∨ goodInfo j = some (v, GTag.M) ∨ goodInfo j = some (v, GTag.H)

/-- **The floor buyers' approved target expenditure** `W_v` (italic; arXiv:2610.35848, (15), p.16,
and Lemma B.5, p.42 (PDF 44): "the actual approved expenditures of floor … buyers … on the three
targets of v"): `∑_{i ∈ F_v} ∑_{j target of v, u_ij > 0} p_j x_ij`. -/
noncomputable def floorTargetExp {a τ : ℚ} {K : ℕ} {G : ThrGraph}
    (x : Buyer a τ K G → Good a τ K G → ℝ) (p : Good a τ K G → ℝ) (v : Fin G.n) : ℝ :=
  ∑ i, ∑ j, if buyerInfo i = some (v, BTag.F) ∧ IsTargetOf v j ∧ 0 < mkt a τ K G i j
    then p j * x i j else 0

/-- **The upper buyers' approved target expenditure** `V_v` (arXiv:2610.35848, (15), p.16, and
Lemma B.5, p.42): `∑_{i ∈ B^{MH}_v} ∑_{j target of v, u_ij > 0} p_j x_ij`. -/
noncomputable def upperTargetExp {a τ : ℚ} {K : ℕ} {G : ThrGraph}
    (x : Buyer a τ K G → Good a τ K G → ℝ) (p : Good a τ K G → ℝ) (v : Fin G.n) : ℝ :=
  ∑ i, ∑ j, if buyerInfo i = some (v, BTag.BMH) ∧ IsTargetOf v j ∧ 0 < mkt a τ K G i j
    then p j * x i j else 0

end HZTractability


