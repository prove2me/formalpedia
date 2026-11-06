-- Prove2me | Definitions.Def_AdvMultiplayer_drawSlow
-- name    : AdvMultiplayer_drawSlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:47.332763+00:00
-- url     : https://prove2.me/theorems/2d4005ea-0488-424a-94e9-2e905f202f18
-- title:
--   The sequential sampler and the fast-arm draw
-- statement:
--   To sample an $m$-set from a signed combination $f=\sum_c a_cQ_{w^c}$, the coordinator considers the arms in order and includes the next arm exactly when $W_{\mathrm{in}}>VW$, where $V$ is the next assignment coordinate, $W$ is the mass of the $m$-sets consistent with the choices so far, and $W_{\mathrm{in}}$ the mass of those also containing the arm. The masses are computed from suffix elementary symmetric sums in $O(Km)$ operations. The last assignment coordinate designates the fast arm by inverse CDF of (4), and the remaining arms are the slow set. The fast arm is drawn by inverse CDF of $q^\gamma_{w}(\cdot\mid U)$ from the coordinate fast.
--
--   **Formalization Note.** Normalizers and masses are checked as in App. A.1.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 8, p.49; App. A.1 paragraph 5, p.53; Algorithm 3 line 3

import Mathlib
import Definitions.Def_AdvMultiplayer_Local
import Definitions.Def_AdvMultiplayer_RowReader

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The arm labels `1, …, K`. -/
def armList : List ℕ := List.range' 1 p.K

/-- The check `x ≤ y` of a real comparison, ticked. -/
noncomputable def ensureLe (x y : ℝ) : Chk Unit := do
  let b ← rle x y
  if b then pure () else failure

/-- The check `x < y` of a real comparison, ticked. -/
noncomputable def ensureLt (x y : ℝ) : Chk Unit := do
  let b ← rlt x y
  if b then pure () else failure

/-- The elementary symmetric sums `e_k(w_i, …, w_K)` of the arms with label at least `i`, for
`0 ≤ k ≤ m`, by the recursion in `i`: `O(Km)` operations (Section 8, p.49). -/
noncomputable def suffixProg (w : ℕ → ℝ) : StateM ℕ (ℕ → ℕ → ℝ) := do
  let mut E : ℕ → ℕ → ℝ := fun i k => if i = p.K + 1 ∧ k = 0 then 1 else 0
  for i' in List.range p.K do
    let i := p.K - i'
    let mut row : ℕ → ℝ := fun _ => 0
    for k in List.range (p.m + 1) do
      tick 1
      let a := E (i + 1) k
      if k = 0 then
        row := Function.update row k a
      else
        let b ← rmul (w i) (E (i + 1) (k - 1))
        let c ← radd a b
        row := Function.update row k c
    E := Function.update E i row
  pure E

/-- One product law in a signed combination `f = Σ_c coef_c Q_{w^c}`, with its suffix sums,
normalizer `Z(w^c)` and the running product of chosen weights. -/
structure LawData where
  coef : ℝ
  w : ℕ → ℝ
  E : ℕ → ℕ → ℝ
  Z : ℝ
  prod : ℝ

/-- The mass `W` of the `m`-sets consistent with the choices so far (`ch` arms chosen among those
before `i`), and the mass `W_in` of those also containing arm `i` (p.49, App. A.1 ¶5). -/
noncomputable def massProg (laws : List LawData) (i ch : ℕ) : StateM ℕ (ℝ × ℝ) := do
  let mut W : ℝ := 0
  let mut Win : ℝ := 0
  for l in laws do
    tick 1
    let a0 ← rmul l.prod (l.E i (p.m - ch))
    let a1 ← rmul a0 l.coef
    let a2 ← rdiv a1 l.Z
    W ← radd W a2
    if ch < p.m then
      let b0 ← rmul l.prod (l.w i)
      let b1 ← rmul b0 (l.E (i + 1) (p.m - ch - 1))
      let b2 ← rmul b1 l.coef
      let b3 ← rdiv b2 l.Z
      Win ← radd Win b3
  pure (W, Win)

/-- **The sequential sampler and orientation** (Section 8, p.49; App. A.1 ¶5, p.53; Lemma 19 Step 5,
p.38). Gan, arXiv:2610.05688.

The law of the `m`-set is the signed combination `f = Σ_c coef_c Q_{w^c}` given by `spec`: `Q_{w_t}`,
or `Q_{w_t} + κ_t(Q_{w_u} - Q_{w_{u-1}})`. The arms are considered in increasing order, and arm `i` is
included exactly when `W_in > V W`, with `V` the coordinate `assign_i`. The checks of App. A.1 test
`0 < W` and `0 ≤ W_in ≤ W`. The coordinate `assign_{K+1}` then designates the fast arm by inverse CDF
of the orientation (4) on the anchor. The result is the slow set in increasing order.

**Formalization Note.** The law of the slow set comes from the orientation of the sampled `m`-set; it
is not drawn directly from `p_w`. -/
noncomputable def drawSlow (d : TableData p) (q t : ℕ) (spec : List (ℝ × (ℕ → ℝ)))
    (anchor : ℕ → ℝ) : Chk (List ℕ) := do
  let mut laws : List LawData := []
  for c in spec do
    tick 1
    let E ← suffixProg p c.2
    laws := laws ++ [⟨c.1, c.2, E, E 1 p.m, 1⟩]
  for l in laws do
    ensureLt 0 l.Z
  let mut ch : ℕ := 0
  let mut S : List ℕ := []
  for i in armList p do
    tick 1
    let (W, Win) ← massProg p laws i ch
    ensureLt 0 W
    ensureLe 0 Win
    ensureLe Win W
    let v ← readAssign p d q t i
    let vw ← rmul v W
    let inc ← rlt vw Win
    if inc then
      ch := ch + 1
      S := S ++ [i]
      tick spec.length
      laws := laws.map fun l => { l with prod := l.prod * l.w i }
  ensure (ch = p.m)
  -- the orientation (4)
  let mut tot : ℝ := 0
  for a in S do
    tick 1
    let x ← rdiv 1 (anchor a)
    tot ← radd tot x
  ensureLt 0 tot
  let v ← readAssign p d q t (p.K + 1)
  let mut cum : ℝ := 0
  let mut j : ℕ := 0
  for a in S do
    tick 1
    let x ← rdiv 1 (anchor a)
    let y ← rdiv x tot
    cum ← radd cum y
    let hit ← rlt v cum
    if hit && j == 0 then j := a
  ensure (j ≠ 0)
  tick p.m
  pure (S.filter (· ≠ j))

/-- The current weight `(1+1/D)^z` of a score `z`, by repeated squaring (p.50). -/
noncomputable def weightProg (z : ℕ) : StateM ℕ ℝ := do
  let x ← rdiv 1 (p.D : ℝ)
  let y ← radd 1 x
  powProg p.Lfield y z

/-- The fast-arm draw of Algorithm 3, line 3: the arm given by inverse CDF of `q^γ_w(·|U)` (5), (7),
over the arms outside `U` in increasing order, with the coordinate `fast`, and its probability. It
uses only the anchor, the outside scores and `U`. -/
noncomputable def fastDraw (d : TableData p) (q t : ℕ) (c : Co p) : Chk (ℕ × ℝ) := do
  let mut s : ℝ := 0
  let mut mass : ℕ → ℝ := fun _ => 0
  for a in armList p do
    tick 1
    if c.inU a then
      let x ← rdiv 1 (c.wbar a)
      s ← radd s x
  let mut tot : ℝ := 0
  for a in armList p do
    tick 1
    if !(c.inU a) then
      let w ← weightProg p (c.z a)
      let x ← rmul s (c.wbar a)
      let y ← radd 1 x
      let v ← rdiv w y
      mass := Function.update mass a v
      tot ← radd tot v
  ensureLt 0 tot
  let g := p.gammaOf p.eta
  ensureLe 0 g
  ensureLe g 1
  let v ← readFast p d q t
  let mut cum : ℝ := 0
  let mut j : ℕ := 0
  let mut pi : ℝ := 0
  for a in armList p do
    tick 1
    if !(c.inU a) then
      let x ← rdiv (mass a) tot
      let y ← rmul (1 - g) x
      let u ← rdiv g ((p.K - p.m + 1 : ℕ) : ℝ)
      let qa ← radd y u
      cum ← radd cum qa
      let hit ← rlt v cum
      if hit && j == 0 then
        j := a
        pi := qa
  ensure (j ≠ 0)
  pure (j, pi)

end AdvMultiplayer


