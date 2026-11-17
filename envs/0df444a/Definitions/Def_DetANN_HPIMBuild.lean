-- Prove2me | Definitions.Def_DetANN_HPIMBuild
-- name    : DetANN_HPIMBuild
-- status  : Definition
-- author  : @milia
-- created : 2026-11-16T06:17:09.834596+00:00
-- url     : https://prove2.me/theorems/253e4d3b-3997-4dc1-9a40-ff8ab6d65efb
-- title:
--   The certified near-neighbour BSP
-- statement:
--   Let $P_1,\dots,P_n\in\mathbb R^m$, $r>0$ and $c\ge1$. For a box $B=[lo,hi]\subseteq\mathbb R^m$, let $\mathrm{dist}(B,p)$ and $\mathrm{maxdist}(B,p)$ be the least and the largest distance from $B$ to $p$ (computed exactly, as squares), and let $\sigma(B)$ be the longest side of $B$.
--
--   **Construction** of the BSP $\mathrm{build}(f,B)$ with fuel $f$ (definition `DetANN_HPIMBSP`). Let $\mathrm{near}(B)=\{i:\mathrm{dist}(B,P_i)\le r\}$.
--   1. If $f=0$, or $\mathrm{near}(B)=\emptyset$, then $B$ is an $\mathrm{OUT}$ leaf.
--   2. Else, if some $i\in\mathrm{near}(B)$ has $\mathrm{maxdist}(B,P_i)\le cr$, then $B$ is an $\mathrm{IN}(i)$ leaf, for the least such $i$.
--   3. Else let $a_j,b_j$ be the least and largest $j$-th coordinates of the near points, and let the **core** be
--   $$T=\prod_j\,[a_j-2r,\ b_j+2r]\cap[lo_j,hi_j].$$
--      - If $2\sigma(T)\le\sigma(B)$, **carve**: peel the axes $j=0,\dots,m-1$ in order, cutting off from the current box first the slab below $a_j-2r$, then the slab above $b_j+2r$. Every slab and the final core are built with fuel $f-1$.
--      - Otherwise **split** $B$ at the midpoint of its longest side (the least such axis), and build both halves with fuel $f-1$.
--
--   `carveBoxes` lists the boxes created by a carve. **Starves** holds if the recursion reaches fuel $0$ on some branch.
--
--   **Certificates.** A leaf is **certified** if it is $\mathrm{OUT}$ and $\mathrm{dist}(B,P_i)>r$ for every $i$, or $\mathrm{IN}(i)$ and $\mathrm{maxdist}(B,P_i)\le cr$.
--
--   **Root box and fuel.** The root box is the bounding box of the points, grown by $D+4r$ on every side, where $D$ is its longest side. The fuel of a lookup structure is $\lceil n(2^{12}/\varepsilon)^{2m}\rceil+1$ with $\varepsilon=\delta/4$.
--
--   Every cut is at a box corner, a data coordinate $\pm2r$, or a midpoint, so no floor operation is needed. This replaces the grids of the tree of Har-Peled, Indyk and Motwani (2012, §2), which the PNormReg machine cannot compute.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). It replaces the grids of Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, which need a floor operation.

import Mathlib
import Definitions.Def_DetANN_HPIMBSP

/-!
# The certified near-neighbour BSP

For points `pts : Fin n → ℝ^m`, a radius `r` and a factor `c`, `build pts r c f lo hi` is a binary space
partition of the box `[lo, hi]` whose leaves answer the near-neighbour question at radius `r`:
an `IN(i)` leaf lies within `c r` of point `i`, an `OUT` leaf is farther than `r` from every point.
A live box (some point within `r`, none within `c r` of the whole box) is either *carved* down to the
core `[a − 2r, b + 2r] ∩ [lo, hi]` around its near points `[a, b]` (when the core has at most half the
longest side), or *split* at the midpoint of its longest side. Cuts are computed with additions and
halvings only: no floor, no grid.

* `boxDist2`, `boxMaxDist2`: squared least and largest distance from a box to a point; `sigma`: the
  longest side; `longestAxis`: the least axis among the longest sides; `setCoord`.
* `carve`, `carveBoxes`: the carve into slabs and core (axes in order, low slab first), and the list of
  boxes it creates.
* `build` (with fuel `f`), `bspFuel n m δ`: the fuel used by the lookup structures.
* `rootLo`, `rootHi`: the root box, the bounding box of the points grown by `D + 4r` on every side,
  with `D` its longest side.
* `BSP.Certified`: every leaf carries a valid certificate.
* `Starves`: the recursion of `build` reaches fuel `0` on some branch.
-/

namespace DetANN.HPIM

variable {m : ℕ}

/-- Squared distance from the box `[lo, hi]` to `p`. -/
noncomputable def boxDist2 (lo hi p : Fin m → ℝ) : ℝ :=
  ∑ j, (max (lo j - p j) (max 0 (p j - hi j))) ^ 2

/-- Squared largest distance from the box `[lo, hi]` to `p`. -/
noncomputable def boxMaxDist2 (lo hi p : Fin m → ℝ) : ℝ :=
  ∑ j, (max (p j - lo j) (hi j - p j)) ^ 2

/-- The longest side `σ`. -/
noncomputable def sigma (lo hi : Fin m → ℝ) : ℝ := ⨆ j, (hi j - lo j)

/-- The least axis among the longest sides (`none` only if `m = 0`). -/
noncomputable def longestAxis (lo hi : Fin m → ℝ) : Option (Fin m) := by
  classical
  exact if h : (Finset.univ.filter fun j : Fin m => sigma lo hi ≤ hi j - lo j).Nonempty
    then some ((Finset.univ.filter fun j : Fin m => sigma lo hi ≤ hi j - lo j).min' h) else none

/-- Replace coordinate `k` of `v` by `x`. -/
def setCoord (v : Fin m → ℝ) (k : ℕ) (x : ℝ) : Fin m → ℝ := fun j => if (j : ℕ) = k then x else v j

/-- The carve of `[lo, hi]` to the core `[tlo, thi]`: axes `k, k+1, …` in order. In each axis the
low slab is peeled first, then the high slab. `bld` builds a child box (slabs and core). The argument
`d` counts the axes still to do. -/
noncomputable def carve (tlo thi : Fin m → ℝ) (bld : (Fin m → ℝ) → (Fin m → ℝ) → BSP m) :
    ℕ → ℕ → (Fin m → ℝ) → (Fin m → ℝ) → BSP m
  | 0, _, lo, hi => bld lo hi
  | d + 1, k, lo, hi =>
    if hk : k < m then
      let low := lo ⟨k, hk⟩ < tlo ⟨k, hk⟩
      let lo' := if low then setCoord lo k (tlo ⟨k, hk⟩) else lo
      let rest : BSP m :=
        if hi ⟨k, hk⟩ > thi ⟨k, hk⟩ then
          .cut lo' hi (carve tlo thi bld d (k + 1) lo' (setCoord hi k (thi ⟨k, hk⟩)))
            (bld (setCoord lo' k (thi ⟨k, hk⟩)) hi)
        else carve tlo thi bld d (k + 1) lo' hi
      if low then .cut lo hi (bld lo (setCoord hi k (tlo ⟨k, hk⟩))) rest else rest
    else bld lo hi

/-- The certified near-neighbour BSP on the local points `pts`, at radius `r` and factor
`c`, built in the box `[lo, hi]` with fuel `f`. -/
noncomputable def build {n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ) :
    ℕ → (Fin m → ℝ) → (Fin m → ℝ) → BSP m
  | 0, lo, hi => .leaf lo hi none
  | f + 1, lo, hi => by
    classical
    let near := Finset.univ.filter fun i => boxDist2 lo hi (pts i) ≤ r ^ 2
    exact if hn : near.Nonempty then
      let good := near.filter fun i => boxMaxDist2 lo hi (pts i) ≤ (c * r) ^ 2
      if hg : good.Nonempty then .leaf lo hi (some (good.min' hg : ℕ)) else
        let tlo : Fin m → ℝ := fun j => max (near.inf' hn (fun i => pts i j) - 2 * r) (lo j)
        let thi : Fin m → ℝ := fun j => min (near.sup' hn (fun i => pts i j) + 2 * r) (hi j)
        if 2 * sigma tlo thi ≤ sigma lo hi then carve tlo thi (build pts r c f) m 0 lo hi
        else
          match longestAxis lo hi with
          | none => .leaf lo hi none
          | some k =>
            let mid := (lo k + hi k) / 2
            .cut lo hi (build pts r c f lo (setCoord hi k mid)) (build pts r c f (setCoord lo k mid) hi)
    else .leaf lo hi none

/-- The child boxes that `carve` hands to its builder `bld`, in order. -/
noncomputable def carveBoxes (tlo thi : Fin m → ℝ) :
    ℕ → ℕ → (Fin m → ℝ) → (Fin m → ℝ) → List ((Fin m → ℝ) × (Fin m → ℝ))
  | 0, _, lo, hi => [(lo, hi)]
  | d + 1, k, lo, hi =>
    if hk : k < m then
      let low := lo ⟨k, hk⟩ < tlo ⟨k, hk⟩
      let lo' := if low then setCoord lo k (tlo ⟨k, hk⟩) else lo
      let rest :=
        if hi ⟨k, hk⟩ > thi ⟨k, hk⟩ then
          carveBoxes tlo thi d (k + 1) lo' (setCoord hi k (thi ⟨k, hk⟩)) ++
            [(setCoord lo' k (thi ⟨k, hk⟩), hi)]
        else carveBoxes tlo thi d (k + 1) lo' hi
      if low then (lo, setCoord hi k (tlo ⟨k, hk⟩)) :: rest else rest
    else [(lo, hi)]

/-- The recursion of `build` reaches fuel `0` on some branch (and then answers an uncertified
`OUT`). The case `longestAxis = none` (only possible for `m = 0`) also counts as starving. -/
noncomputable def Starves {n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ) :
    ℕ → (Fin m → ℝ) → (Fin m → ℝ) → Prop
  | 0, _, _ => True
  | f + 1, lo, hi => by
    classical
    let near := Finset.univ.filter fun i => boxDist2 lo hi (pts i) ≤ r ^ 2
    exact if hn : near.Nonempty then
      let good := near.filter fun i => boxMaxDist2 lo hi (pts i) ≤ (c * r) ^ 2
      if good.Nonempty then False else
        let tlo : Fin m → ℝ := fun j => max (near.inf' hn (fun i => pts i j) - 2 * r) (lo j)
        let thi : Fin m → ℝ := fun j => min (near.sup' hn (fun i => pts i j) + 2 * r) (hi j)
        if 2 * sigma tlo thi ≤ sigma lo hi then
          ∃ B ∈ carveBoxes tlo thi m 0 lo hi, Starves pts r c f B.1 B.2
        else
          match longestAxis lo hi with
          | none => True
          | some k =>
            let mid := (lo k + hi k) / 2
            Starves pts r c f lo (setCoord hi k mid) ∨ Starves pts r c f (setCoord lo k mid) hi
    else False

/-- The fuel of the lookup structures: one more than the node bound `n (2^12/ε)^{2m}`, `ε = δ/4`. -/
noncomputable def bspFuel (n m : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) * (2 ^ 12 / (δ / 4)) ^ (2 * m)⌉₊ + 1

namespace BSP

/-- Every leaf carries a valid certificate: `OUT` leaves are farther than `r` from every point, and
`IN(i)` leaves are within `c r` of point `i`. -/
def Certified {n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ) : BSP m → Prop
  | .leaf lo hi none => ∀ i, r ^ 2 < boxDist2 lo hi (pts i)
  | .leaf lo hi (some i) => ∃ h : i < n, boxMaxDist2 lo hi (pts ⟨i, h⟩) ≤ (c * r) ^ 2
  | .cut _ _ l t => Certified pts r c l ∧ Certified pts r c t

end BSP

/-- The root box of a lookup structure: the bounding box grown by `D + 4r`. -/
noncomputable def rootLo {n : ℕ} (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (r : ℝ) : Fin m → ℝ :=
  fun j => Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j) -
    (sigma (fun j => Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j))
      (fun j => Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j)) + 4 * r)

noncomputable def rootHi {n : ℕ} (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (r : ℝ) : Fin m → ℝ :=
  fun j => Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j) +
    (sigma (fun j => Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j))
      (fun j => Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j)) + 4 * r)

end DetANN.HPIM


