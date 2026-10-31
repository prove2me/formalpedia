-- Prove2me | Definitions.Def_TractableComposite_facetGen
-- name    : TractableComposite_facetGen
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:54:34.82684+00:00
-- url     : https://prove2.me/theorems/b286b024-06c2-4d58-a425-9c23c6eceee7
-- title:
--   The facet-generation program for $\operatorname{conc}_P(\bar\phi)$
-- statement:
--   The algorithm of Theorem 2's proof, in the real-RAM tick model. On input $\bar u\in P$ it
--
--   1. computes the lifting $\bar s$ with the program for (4);
--   2. computes $J_i=\{j\mid\bar u_{ij}=\bar s_{ij}\}$ by ticked equality tests;
--   3. runs Algorithm 1 at $\bar s$, obtaining $(\alpha^\pi,b^\pi)$;
--   4. returns $(\alpha',b')$ with $\langle\alpha',s\rangle+b'=\langle\alpha^\pi,\Gamma_J(s)\rangle+b^\pi$, i.e. $b'=b^\pi$ and $\alpha'=\Gamma_J^{\top}\alpha^\pi$, computed by one right-to-left and one left-to-right pass per row.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Theorem 2 and its proof, p.14

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_req
import Definitions.Def_LNTopology_Hermetization_rmul
import Definitions.Def_LNTopology_Hermetization_rdiv
import Definitions.Def_TractableComposite_radd
import Definitions.Def_TractableComposite_rsub
import Definitions.Def_TractableComposite_liftProg
import Definitions.Def_TractableComposite_alg1Prog

namespace TractableComposite

/-- **The facet-generation program for conc_P(φ̄)**, Theorem 2 and its proof, p.14. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.14.

On input `ū`:
1. `s̄ ← liftProg a ū`, the lifting `(ū, s̄) ∈ PQ'` (4);
2. `Jᵢ = {j | ūᵢⱼ = s̄ᵢⱼ}`, computed by ticked equality tests;
3. `(α^π, b^π) ← alg1Prog a φ s̄` (Algorithm 1);
4. return `(α', b')` with `⟨α', s⟩ + b' = ⟨α^π, Γ_J(s)⟩ + b^π` (proof of Theorem 2), i.e. `b' = b^π` and
   `α' = Γ_Jᵀ α^π`: `α'ᵢⱼ` collects `α^π_ij` for `j ∈ Jᵢ`, and for `j ∉ Jᵢ` the weight `α^π_ij` is spread onto
   `l(i,j)` and `r(i,j)` with factors `1 − γᵢⱼ` and `γᵢⱼ` (6); `r(i,·)` is found by a right-to-left pass and
   `l(i,·)` by a left-to-right pass, both ticked.

**Cost model** (reading R3; the published discipline of `LNTopology.Hermetization.tick`): every real
arithmetic operation (`radd`, `rsub`, `rmul`, `rdiv`), every real comparison (`rle`, `req`) and every
query of `φ` (`phiAt`) costs one tick; every iteration of every loop and every recursive call ticks at
least once, and the unticked work inside one iteration is a bounded number of reads and updates of
array-like state (`Fin d → Fin (n+1) → ℝ`, `Fin d → Fin (n+1)`, `Fin d → Fin (n+1) → Bool`, the head of
a list, index arithmetic on `ℕ`/`Fin`); the only decisions on real data are the ticked primitives; the
program never reads the counter. The running time of a run started at `0` is the final counter. -/
noncomputable def facetGen {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (φ : (Fin d → ℝ) → ℝ) (u : Fin d → Fin (n + 1) → ℝ) :
    StateM ℕ ((Fin d → Fin (n + 1) → ℝ) × ℝ) := do
  -- step 1: the lifting
  let s ← liftProg a u
  -- step 2: J
  let mut inJ : Fin d → Fin (n + 1) → Bool := fun _ _ => false
  for i in List.finRange d do
    LNTopology.Hermetization.tick 1
    for j in List.finRange (n + 1) do
      LNTopology.Hermetization.tick 1
      let e ← LNTopology.Hermetization.req (u i j) (s i j)
      inJ := Function.update inJ i (Function.update (inJ i) j e)
  -- step 3: Algorithm 1 at s̄
  let out ← alg1Prog a φ s
  let α := out.1
  -- step 4: α' = Γ_Jᵀ α^π
  let mut α' : Fin d → Fin (n + 1) → ℝ := fun _ _ => 0
  for i in List.finRange d do
    LNTopology.Hermetization.tick 1
    -- r(i, j): right-to-left pass
    let mut nxt : Fin (n + 1) → Fin (n + 1) := fun _ => Fin.last n
    let mut cur : Fin (n + 1) := Fin.last n
    for jj in List.range (n + 1) do
      LNTopology.Hermetization.tick 1
      let j : Fin (n + 1) := ⟨n - jj, by omega⟩
      if inJ i j then cur := j
      nxt := Function.update nxt j cur
    -- l(i, j) and the spreading: left-to-right pass
    let mut lft : Fin (n + 1) := 0
    for j in List.finRange (n + 1) do
      LNTopology.Hermetization.tick 1
      if inJ i j then
        lft := j
        let v ← radd (α' i j) (α i j)
        α' := Function.update α' i (Function.update (α' i) j v)
      else
        let r := nxt j
        let num ← rsub (a i j) (a i lft)
        let den ← rsub (a i r) (a i lft)
        let γ ← LNTopology.Hermetization.rdiv num den
        let γc ← rsub 1 γ
        let wl ← LNTopology.Hermetization.rmul γc (α i j)
        let vl ← radd (α' i lft) wl
        α' := Function.update α' i (Function.update (α' i) lft vl)
        let wr ← LNTopology.Hermetization.rmul γ (α i j)
        let vr ← radd (α' i r) wr
        α' := Function.update α' i (Function.update (α' i) r vr)
  return (α', out.2)

end TractableComposite


