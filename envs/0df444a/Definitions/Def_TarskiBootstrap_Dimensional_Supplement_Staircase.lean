-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Supplement_Staircase
-- name    : TarskiBootstrap_Dimensional_Supplement_Staircase
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:55.832462+00:00
-- url     : https://prove2.me/theorems/cfb0ef8f-9a47-4657-ace4-68f7ed31ff6c
-- title:
--   The staircase $S$ and the staircase constructor $\hat{\mathcal E}$
-- statement:
--   Let $Q=\{1,\dots,m\}\times[n]^k$ with the lexicographic order: $(i,x)\preceq(j,y)$ iff $i<j$, or $i=j$ and $x\preceq y$. Give $Q^2$ the product order and let
--
--   $$
--   S=\bigcup_{i=1}^m D_i\ \cup\ \bigcup_{i=1}^{m-1}B_i,\qquad D_i=P_i\times P_i,\quad B_i=P_i\times P_{i+1},\quad P_i=\{(i,x)\},
--   $$
--
--   with the induced order. With $\sigma_i=\sigma^{f_i}_{s_i}$, the transition directions are
--
--   $$
--   \varphi_i(x,y)=\begin{cases}+1,&\sigma_i(x)=+1,\\-1,&\sigma_i(x)<+1\wedge\sigma_i(y)=-1,\\0,&\text{otherwise,}\end{cases}\qquad
--   \psi_i(x,y)=\begin{cases}-1,&\sigma_i(x)<+1,\\0,&\sigma_i(x)=+1\wedge\sigma_{i+1}(y)=-1,\\+1,&\sigma_i(x)=+1\wedge\sigma_{i+1}(y)>-1.\end{cases}
--   $$
--
--   The staircase constructor $F=\hat{\mathcal E}(s,f):S\to S$ is, on $D_i$ with $d=\varphi_i(x,y)$,
--
--   $$
--   F((i,x),(i,y))=\begin{cases}((i-1,\top),(i,f_i(y))),& d=-1\wedge i>1,\\((i,f_i(x)),(i+1,\bot)),& d=+1\wedge i<m,\\((i,f_i(x)),(i,f_i(y))),&\text{otherwise,}\end{cases}
--   $$
--
--   and on $B_i$ with $d=\psi_i(x,y)$,
--
--   $$
--   F((i,x),(i+1,y))=\begin{cases}((i,f_i(x)),(i,\top)),& d=-1,\\((i,f_i(x)),(i+1,f_{i+1}(y))),& d=0,\\((i+1,\bot),(i+1,f_{i+1}(y))),& d=+1,\end{cases}
--   $$
--
--   where $\top=(n-1)\mathbf 1$ and $\bot=0$.
--
--   **Formalization Note** $Q$ is Mathlib's lexicographic product `Fin m ×ₗ Grid n k`; $S$ is a subtype of $Q\times Q$ with the induced product order; block indices $1,\dots,m$ are `Fin m`, so $i>1$ reads `0 < i.val` and $i<m$ reads `i.val + 1 < m`.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, equations (4.8), (4.10), (4.13)–(4.16) and Definition 4.8, PDF/printed pp. 19–21, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_HiddenSign

namespace TarskiBootstrap.Dimensional.Supplement

/-- `Q = {1, …, m} × [n]^k` of (4.8), PDF/printed p. 19, with the lexicographic order:
`(i, x) ⪯ (j, y)` iff `i < j`, or `i = j` and `x ⪯ y` (block indices encoded by
`Fin m`). -/
abbrev StairQ (n k m : ℕ+) := Fin (m : ℕ) ×ₗ Grid n k

/-- Membership in the staircase `S = ⋃ D_i ∪ ⋃ B_i ⊆ Q²` of (4.10), p. 20: a main block
point `((i, x), (i, y)) ∈ D_i` or a bridge point `((i, x), (i + 1, y)) ∈ B_i`. -/
def IsStaircase {n k m : ℕ+} (u : StairQ n k m × StairQ n k m) : Prop :=
  (ofLex u.2).1 = (ofLex u.1).1 ∨ (ofLex u.2).1.val = (ofLex u.1).1.val + 1

/-- The staircase `S` with the order induced from the product order on `Q²`. -/
abbrev Staircase (n k m : ℕ+) := {u : StairQ n k m × StairQ n k m // IsStaircase u}

/-- The transition direction `φ_i` on the main block `D_i`, (4.13), p. 21, for the sign
function `σ = σ_{s_i}^{f_i}`. -/
def stairPhi {n k : ℕ+} (σ : Grid n k → SignType) (x y : Grid n k) : SignType :=
  if σ x = 1 then 1 else if σ x < 1 ∧ σ y = -1 then -1 else 0

/-- The transition direction `ψ_i` on the bridge `B_i`, (4.14), p. 21, for
`σ = σ_{s_i}^{f_i}` and `σ' = σ_{s_{i+1}}^{f_{i+1}}`. -/
def stairPsi {n k : ℕ+} (σ σ' : Grid n k → SignType) (x y : Grid n k) : SignType :=
  if σ x < 1 then -1 else if σ x = 1 ∧ σ' y = -1 then 0 else 1

/-- The staircase constructor `Ê(s, f) : S → S` of Definition 4.8, (4.15)–(4.16),
PDF/printed p. 21, with `σ_r = σ_{s_r}^{f_r}` the hidden sign functions of (4.2) for the
antichain `A`, `⊤ = (n-1)𝟏` and `⊥ = 0`. On `D_i` with `d = φ_i(x, y)`:
`((i-1, ⊤), (i, f_i(y)))` if `d = -1 ∧ i > 1`; `((i, f_i(x)), (i+1, ⊥))` if
`d = +1 ∧ i < m`; otherwise `((i, f_i(x)), (i, f_i(y)))`. On `B_i` with `d = ψ_i(x, y)`:
`((i, f_i(x)), (i, ⊤))` if `d = -1`; `((i, f_i(x)), (i+1, f_{i+1}(y)))` if `d = 0`;
`((i+1, ⊥), (i+1, f_{i+1}(y)))` if `d = +1`. -/
noncomputable def staircase {n k m : ℕ+} (A : Set (Grid n k))
    (s : Fin (m : ℕ) → SignType) (f : Fin (m : ℕ) → Grid n k → Grid n k)
    (u : Staircase n k m) : Staircase n k m :=
  let i := (ofLex u.val.1).1
  let x := (ofLex u.val.1).2
  let j := (ofLex u.val.2).1
  let y := (ofLex u.val.2).2
  let σ : Fin (m : ℕ) → Grid n k → SignType := fun r => hiddenSign A (s r) (f r)
  if j = i then
    if h1 : stairPhi (σ i) x y = -1 ∧ 0 < i.val then
      ⟨(toLex (⟨i.val - 1, by omega⟩, ⊤), toLex (i, f i y)),
        Or.inr (by show i.val = (i.val - 1) + 1; omega)⟩
    else if h2 : stairPhi (σ i) x y = 1 ∧ i.val + 1 < (m : ℕ) then
      ⟨(toLex (i, f i x), toLex (⟨i.val + 1, h2.2⟩, ⊥)), Or.inr rfl⟩
    else
      ⟨(toLex (i, f i x), toLex (i, f i y)), Or.inl rfl⟩
  else
    if stairPsi (σ i) (σ j) x y = -1 then
      ⟨(toLex (i, f i x), toLex (i, ⊤)), Or.inl rfl⟩
    else if stairPsi (σ i) (σ j) x y = 0 then
      ⟨(toLex (i, f i x), toLex (j, f j y)), u.property⟩
    else
      ⟨(toLex (j, ⊥), toLex (j, f j y)), Or.inl rfl⟩

end TarskiBootstrap.Dimensional.Supplement


