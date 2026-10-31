-- Prove2me | Definitions.Def_TractableComposite_alg1Prog
-- name    : TractableComposite_alg1Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:53:19.100992+00:00
-- url     : https://prove2.me/theorems/001e6130-468a-4661-b4be-b527018e7316
-- title:
--   Algorithm 1 (Facet-Generation over $Q$)
-- statement:
--   The program of Algorithm 1 in the real-RAM tick model. On input $\bar s$ it
--
--   1. computes $\bar z=Z(\bar s)$ by (11);
--   2. sorts the coordinates $\bar z_{ij}$, $j\ge1$, in non-increasing order by merging the $d$ rows (ties to the smaller $i$, so equal values of one row stay adjacent); the row of the $k$-th entry is the $k$-th move $\pi(k)$;
--   3. walks the staircase from the grid point $0$, querying $\phi$ at each of the $dn+1$ grid points and recording the slopes $\vartheta(\pi,i,j)$;
--   4. returns $(\alpha^\pi,b^\pi)$ computed by (15).
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Algorithm 1, p.12; (11), p.9; (15), p.11

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_rmul
import Definitions.Def_LNTopology_Hermetization_rdiv
import Definitions.Def_TractableComposite_radd
import Definitions.Def_TractableComposite_rsub
import Definitions.Def_TractableComposite_phiAt
import Definitions.Def_TractableComposite_mergeRange

namespace TractableComposite

/-- **Algorithm 1 (Facet-Generation over Q)**, p.12. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Algorithm 1, p.12; (11), p.9; (15), p.11.

On input `s̄`:
1. (line 2) `z̄ ← Z(s̄)` by (11): `z̄ᵢ₀ = 1`, `z̄ᵢⱼ = (s̄ᵢⱼ − s̄_{i,j−1})/(aᵢⱼ − a_{i,j−1})`;
2. (lines 3–7) sort the coordinates `z̄ᵢⱼ`, `j ≥ 1`, in non-increasing order by merging the `d` rows with
   `mergeRange` (each row is already non-increasing when `s̄ ∈ Q`); ties go to the smaller `i`, and within
   a row `j` increases, so equal values of one row stay adjacent (lines 5–6). The `k`-th entry `(i, j)` of
   the merged list is `Θ(k)` and its row is the `k`-th move `π(k) = Θ₁(k)` (p.12);
3. walk the staircase from the grid point `0`: before the first move query `φ(𝒱·ₙ(π,0)) = φ(a₁₀,…,a_d0)`;
   at the `k`-th move, in direction `i`, from column `j−1` to `j`, query `φ(𝒱·ₙ(π,k))` and record
   `ϑ(π,i,j) = (φ(𝒱·ₙ(π,k)) − φ(𝒱·ₙ(π,k−1)))/(aᵢⱼ − a_{i,j−1})` (p.11);
4. (line 8) compute `α^π` and `b^π = φ(𝒱·ₙ(π,0)) − ⟨α^π, 𝒱(π,0)⟩` by (15), and (line 9) return `(α^π, b^π)`.

The current grid point is kept as `g : Fin d → Fin (n+1)`, updated in one coordinate per move; the query
passes its values `(a_{i, gᵢ})ᵢ`.

**Cost model** (reading R3; the published discipline of `LNTopology.Hermetization.tick`): every real
arithmetic operation (`radd`, `rsub`, `rmul`, `rdiv`), every real comparison (`rle`, `req`) and every
query of `φ` (`phiAt`) costs one tick; every iteration of every loop and every recursive call ticks at
least once, and the unticked work inside one iteration is a bounded number of reads and updates of
array-like state (`Fin d → Fin (n+1) → ℝ`, `Fin d → Fin (n+1)`, `Fin d → Fin (n+1) → Bool`, the head of
a list, index arithmetic on `ℕ`/`Fin`); the only decisions on real data are the ticked primitives; the
program never reads the counter. The running time of a run started at `0` is the final counter. -/
noncomputable def alg1Prog {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (φ : (Fin d → ℝ) → ℝ) (s : Fin d → Fin (n + 1) → ℝ) :
    StateM ℕ ((Fin d → Fin (n + 1) → ℝ) × ℝ) := do
  -- line 2: z̄ ← Z(s̄), (11)
  let mut z : Fin d → Fin (n + 1) → ℝ := fun _ _ => 1
  for i in List.finRange d do
    LNTopology.Hermetization.tick 1
    for j in List.finRange (n + 1) do
      LNTopology.Hermetization.tick 1
      if h : j.val = 0 then
        pure ()
      else
        let jm : Fin (n + 1) := ⟨j.val - 1, by omega⟩
        let num ← rsub (s i j) (s i jm)
        let den ← rsub (a i j) (a i jm)
        let q ← LNTopology.Hermetization.rdiv num den
        z := Function.update z i (Function.update (z i) j q)
  -- lines 3–7: sort by merging the d rows
  let order ← mergeRange z 0 d
  -- walk the staircase and record ϑ(π, i, j), p.11
  let mut g : Fin d → Fin (n + 1) := fun _ => 0
  let φ₀ ← phiAt φ (fun i => a i 0)
  let mut φPrev := φ₀
  let mut θ : Fin d → Fin (n + 1) → ℝ := fun _ _ => 0
  for e in order do
    LNTopology.Hermetization.tick 1
    let i := e.1
    let jo := g i
    let jn : Fin (n + 1) := ⟨min (jo.val + 1) n, by omega⟩
    g := Function.update g i jn
    let φCur ← phiAt φ (fun i' => a i' (g i'))
    let num ← rsub φCur φPrev
    let den ← rsub (a i jn) (a i jo)
    let q ← LNTopology.Hermetization.rdiv num den
    θ := Function.update θ i (Function.update (θ i) jn q)
    φPrev := φCur
  -- line 8: α^π by (15)
  let mut α : Fin d → Fin (n + 1) → ℝ := fun _ _ => 0
  for i in List.finRange d do
    LNTopology.Hermetization.tick 1
    for j in List.finRange (n + 1) do
      LNTopology.Hermetization.tick 1
      if j.val = 0 then
        pure ()
      else if h : j.val < n then
        let v ← rsub (θ i j) (θ i ⟨j.val + 1, by omega⟩)
        α := Function.update α i (Function.update (α i) j v)
      else
        α := Function.update α i (Function.update (α i) j (θ i j))
  -- b^π = φ(𝒱·ₙ(π,0)) − ⟨α^π, 𝒱(π,0)⟩, where 𝒱(π,0)ᵢⱼ = aᵢ₀
  let mut acc : ℝ := 0
  for i in List.finRange d do
    LNTopology.Hermetization.tick 1
    for j in List.finRange (n + 1) do
      LNTopology.Hermetization.tick 1
      let p ← LNTopology.Hermetization.rmul (α i j) (a i 0)
      acc ← radd acc p
  let b ← rsub φ₀ acc
  return (α, b)

end TractableComposite


