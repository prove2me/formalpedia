-- Prove2me | Definitions.Def_DetANN_HPIMTree
-- name    : DetANN_HPIMTree
-- status  : Definition
-- author  : @milia
-- created : 2026-11-16T06:35:56.241723+00:00
-- url     : https://prove2.me/theorems/71805e5a-da82-4c74-ae0e-a0db8b019ac4
-- title:
--   The deterministic HPIM tree
-- statement:
--   Let $Y_1,\dots,Y_N\in\mathbb R^m$ and $\delta\in(0,1/2)$, and put $c=1+\delta/4$.
--
--   1. **Lookup contract.** A box decision tree $T$ (definition `DetANN_HPIMFormat`) satisfies the near-neighbour contract for points $P_1,\dots,P_n$ at radius $r$ and factor $c$ if, for every query $q$:
--      - an answer $i$ satisfies $\|q-P_i\|\le cr$;
--      - a null answer implies $\|q-P_j\|>r$ for all $j$.
--   2. **Lookup structure.** `lookupTree` tests whether $q$ is in the root box (definition `DetANN_HPIMBuild`), answering null outside it. Inside, it runs the centroid-balanced (definition `DetANN_HPIMBSP`) certified BSP built with the fuel $\lceil n(2^{12}/\varepsilon)^{2m}\rceil+1$, $\varepsilon=\delta/4$.
--   3. **Node parameters** for a set $S$ of indices with local points $P$ (in increasing index order):
--      - $\lambda=4(\lceil\log_2N\rceil+1)/\delta$;
--      - $r_{\mathrm{med}}$ is half the median threshold of $P$ (definition `DetANN_HPIMThreshold`);
--      - the **radius ladder** is $\rho_k=\tfrac{r_{\mathrm{med}}}{4}c^{k-1}$, and the top radius is $b=2|S|\lambda r_{\mathrm{med}}$;
--      - the **ladder length** $M$ is one more than the least $k$ with $\rho_k\ge b$;
--      - the lookups are $Z_i=\mathrm{lookupTree}(P,\rho_i,c)$ for $i<M$;
--      - the **components** are those of the threshold graph at $r_{\mathrm{med}}$, and the **representatives** those at $2r_{\mathrm{med}}$.
--   4. The **factor** after $L$ levels is $\alpha(L)=(1+1/\lambda)^L c^2$.
--   5. **The tree.** `hpimNode` with fuel $f$ on $S$ is:
--      - a single point if $|S|\le1$ (or $f=0$);
--      - otherwise the node with $n=|S|$ local points, the ladder $Z$, $t_0=\lceil\log_2(M-1)\rceil$, a child (fuel $f-1$) for the component of each local point, and a child for the representatives.
--
--      Finally, $\mathrm{hpimTree}(Y,\delta)$ is $\mathrm{hpimNode}$ with fuel $N+1$ on all of $\{1,\dots,N\}$.
--
--   This is the tree of Har-Peled, Indyk and Motwani (2012, §2), made deterministic and floor-free:
--   - the median radius is exact;
--   - the near-neighbour lookups are certified BSPs, not grids;
--   - the ladder is searched by powers of two.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib
import Definitions.Def_DetANN_HPIMBuild
import Definitions.Def_DetANN_HPIMThreshold

/-!
# The deterministic HPIM tree

A deterministic, floor-free version of the approximate-nearest-neighbour tree of S. Har-Peled,
P. Indyk, R. Motwani, *Approximate nearest neighbor: towards removing the curse of dimensionality*,
Theory of Computing 8 (2012), §2, for `DetANN.lemma_3_3`.

* `NearNbrSpec P r c T`: the near-neighbour contract of a lookup structure `T` (definition
  `DetANN_HPIMFormat`): an answer `i` is within `c r` of the query; a null answer means that no point
  is within `r`.
* `lookupTree pts r c δ`: one lookup structure. It tests the root box (null outside) and then runs the
  centroid-balanced certified BSP (definitions `DetANN_HPIMBuild`, `DetANN_HPIMBSP`).
* The parameters of a node on a point set `S ⊆ Y`: `λ = 4(⌈log₂ N⌉+1)/δ` (`lamOf`), the local points
  in index order (`ptsOf`), `r_med` = half the median threshold (`rmedOf`), the radius ladder
  `ρ_k = (r_med/4)(1+δ/4)^{k-1}` (`rhoOf`), the top radius `b = 2|S| λ r_med` (`bOf`), the ladder
  length `M` = one more than the least `k` with `ρ_k ≥ b` (`MOf`), the lookups `Z_i` at radius `ρ_i`
  and factor `1 + δ/4` (`ZOf`), the components at threshold `r_med` (`compBotOf`) and the
  representatives at `2 r_med` (`repsOf`).
* `alphaOf N δ L = (1 + 1/λ)^L (1 + δ/4)^2`: the approximation factor after `L` levels.
* `hpimNode Y δ f S` (fuel `f`) and `hpimTree Y δ = hpimNode Y δ (N + 1) univ`.
-/

namespace DetANN.HPIM

variable {m : ℕ}

/-- The near-neighbour contract of a lookup structure: an answer `some i` is a local index within
`c r` of `q`, and `none` means that no point is within `r` of `q`. -/
def NearNbrSpec {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m)) (r c : ℝ) (T : BoxTree m) : Prop :=
  ∀ q : EuclideanSpace ℝ (Fin m),
    (∀ i, T.eval q = some i → ∃ h : i < n, ‖q - P ⟨i, h⟩‖ ≤ c * r) ∧
    (T.eval q = none → ∀ j, r < ‖q - P j‖)

/-- One near-neighbour lookup structure on the local points `pts` at radius `r` and factor `c`: the
root-box test (null outside), then the centroid-balanced certified BSP. -/
noncomputable def lookupTree {n : ℕ} (pts : Fin n → Fin m → ℝ) (r c δ : ℝ) : BoxTree m :=
  if hn : 0 < n then
    .test (rootLo hn pts r) (rootHi hn pts r)
      (balance (build pts r c (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r))
        ((build pts r c (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)).paths.card + 1) [] ∅)
      (.leaf none)
  else .leaf none

section Node

open Classical

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

/-- `λ = 4(h+1)/δ`, `h = ⌈log₂ N⌉`. -/
noncomputable def lamOf (N : ℕ) (δ : ℝ) : ℝ := 4 * ((Nat.clog 2 N : ℝ) + 1) / δ

/-- The local points of `S`, in increasing index order. -/
noncomputable def ptsOf (S : Finset (Fin N)) : Fin S.card → EuclideanSpace ℝ (Fin m) :=
  fun i => Y (S.orderEmbOfFin rfl i)

/-- `r_med`: half the median threshold of the local points. -/
noncomputable def rmedOf (S : Finset (Fin N)) : ℝ := medThreshold (ptsOf Y S) / 2

/-- The radius ladder `ρ_k = (r_med/4)(1 + δ/4)^k/(1 + δ/4)`. -/
noncomputable def rhoOf (S : Finset (Fin N)) (k : ℕ) : ℝ :=
  rmedOf Y S / 2 / 2 * (1 + δ / 4) ^ k / (1 + δ / 4)

/-- The top radius `b = 2|S| λ r_med`. -/
noncomputable def bOf (S : Finset (Fin N)) : ℝ := 2 * S.card * lamOf N δ * rmedOf Y S

/-- The ladder length: one more than the least `k` with `ρ_k ≥ b`. -/
noncomputable def MOf (S : Finset (Fin N)) : ℕ :=
  (if h : ∃ k, bOf Y δ S ≤ rhoOf Y δ S k then Nat.find h else 0) + 1

/-- The lookups `Z_i`, at radius `ρ_i` and factor `1 + δ/4`. -/
noncomputable def ZOf (S : Finset (Fin N)) : Fin (MOf Y δ S) → BoxTree m :=
  fun i => lookupTree (fun a j => Y (S.orderEmbOfFin rfl a) j) (rhoOf Y δ S i) (1 + δ / 4) δ

/-- The component of local point `i` at threshold `r_med`, as a subset of `Fin N`. -/
noncomputable def compBotOf (S : Finset (Fin N)) (i : Fin S.card) : Finset (Fin N) :=
  (Finset.univ.filter (thrReach (ptsOf Y S) (2 * (rmedOf Y S / 2)) i)).map
    (S.orderEmbOfFin rfl).toEmbedding

/-- The representatives at threshold `2 r_med`, as a subset of `Fin N`. -/
noncomputable def repsOf (S : Finset (Fin N)) : Finset (Fin N) :=
  (Finset.univ.filter (IsRep (ptsOf Y S) (2 * rmedOf Y S))).map (S.orderEmbOfFin rfl).toEmbedding

/-- The approximation factor after `L` levels: `(1 + 1/λ)^L (1 + δ/4)^2`. -/
noncomputable def alphaOf (N : ℕ) (δ : ℝ) (L : ℕ) : ℝ := (1 + 1 / lamOf N δ) ^ L * (1 + δ / 4) ^ 2

/-- One node of the HPIM tree on the set `S`, with fuel `f`. A set with at most one point is a leaf.
Otherwise the node holds the ladder `Z`, the global indices, a child for the component of each local
point at threshold `r_med`, and a child for the representatives at threshold `2 r_med`. -/
noncomputable def hpimNode {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) :
    ℕ → Finset (Fin N) → HTree m
  | 0, S => .single (if h : S.Nonempty then (S.min' h : ℕ) else 0)
  | f + 1, S =>
    if S.card ≤ 1 then .single (if h : S.Nonempty then (S.min' h : ℕ) else 0) else
      .node S.card (MOf Y δ S) (Nat.clog 2 (MOf Y δ S - 1)) (ZOf Y δ S)
        (fun i => ((S.orderEmbOfFin rfl i : Fin N) : ℕ))
        (fun i => hpimNode Y δ f (compBotOf Y S i)) (hpimNode Y δ f (repsOf Y S))

/-- **The search structure of `lemma_3_3`.** -/
noncomputable def hpimTree {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) : HTree m :=
  hpimNode Y δ (N + 1) Finset.univ

end Node

end DetANN.HPIM


