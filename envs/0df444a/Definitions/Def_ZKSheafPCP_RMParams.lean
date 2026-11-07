-- Prove2me | Definitions.Def_ZKSheafPCP_RMParams
-- name    : ZKSheafPCP_RMParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:12:55.920696+00:00
-- url     : https://prove2.me/theorems/da7c7dc0-6e35-4bb7-885c-20804085f0fd
-- title:
--   The bivariate Reed-Muller sheaf code of Definition 8.1
-- statement:
--   Let $\mathbb F=\mathbb F_{2^l}$ and let $L\subseteq\mathbb F$ be a subspace with basis $b_1,\dots,b_k$, with $k$ even, $k<l$ and $k/2+\hat k+2<k$. Put $L_0=\mathrm{span}(b_1,\dots,b_{k/2})$, $L_R=\mathrm{span}(b_{k/2+1},\dots,b_{k/2+\hat k+2})$, $L_1=\mathrm{span}(b_{k/2+1},\dots,b_k)\setminus L_R$, $L_0'=L_0+L_R$, $L_\beta=\mathrm{span}(L_0',\beta)$, and $q_{L_0}(z)=\prod_{\alpha\in L_0}(z-\alpha)$. The domain is
--   $$D_{\hat k}(L)=\bigcup_{\beta\in L_1}\bigl(L_\beta\times\{q_{L_0}(\beta)\}\bigr)\cup\bigl(L_0'\times q_{L_0}(L)\bigr).$$
--   The coded space consists of its points, the rows $\{x\}\times\{y:(x,y)\in D\}$ for $x\in L_0'$, the columns $\{x:(x,y)\in D\}\times\{y\}$ for $y\in q_{L_0}(L_1)$, and the curve $T=\{(x,q_{L_0}(x)):x\in L\}$. For $d_X+1=2^{\hat k+k/2}$ the local codes are: all of $\mathbb F$ at a point; $\mathrm{RS}[\mathbb F,R_x,d_Y]$ on a row; $\mathrm{RS}[\mathbb F,K_y,d_X]$ on a column; and on $T$ the words with $(c(x,q_{L_0}(x)))_{x\in L}\in\mathrm{RS}[\mathbb F,L,d_X+d_Y|L_0|]$.
--
--   The distribution on the cover $\mathcal R\cup\mathcal K$ picks a uniform row with probability $1/2$ and a uniform column with probability $1/2$.
--
--   **Formalization Note** "A canonical basis" names none, so all statements hold for every basis. The field is any field of characteristic $2$ with $2^l$ elements, and $\mathbb F_2$-independence of the basis says that distinct subsets have distinct sums.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definition 8.1, pp.36–37; App. C, p.49

import Mathlib
import Definitions.Def_ZKSheafPCP_TestTree
import Definitions.Def_ZKSheafPCP_simLaw

namespace ZKSheafPCP

open Classical

/-- The data of Definition 8.1 (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission, manuscript sha256 ac5e528f…,
p.36): `k, k̂, l`, and a basis `b_1, …, b_k` of the subspace `L` of `𝔽 = 𝔽_{2^l}`.

**Formalization Note** Definition 8.1 fixes "a canonical basis" without naming one, so every statement quantifies over all
bases. Indices are `0`-based: the paper's `b_{j+1}` is `b j`. -/
structure RMParams (F : Type) [Field F] where
  /-- the dimension of `L` -/
  k : ℕ
  /-- the parameter `k̂` -/
  khat : ℕ
  /-- `𝔽 = 𝔽_{2^l}` -/
  l : ℕ
  /-- the basis -/
  b : Fin k → F

namespace RMParams

variable {F : Type} [Field F] (R : RMParams F)

/-- `span(b_{lo+1}, …, b_{hi})` over `𝔽₂`, as the set of subset sums. -/
noncomputable def spanRange (lo hi : ℕ) : Finset F :=
  ((Finset.univ.filter fun j : Fin R.k => lo ≤ j.val ∧ j.val < hi).powerset).image fun T => ∑ j ∈ T, R.b j

/-- `L = span(b_1, …, b_k)`. -/
noncomputable def L : Finset F := R.spanRange 0 R.k

/-- `L₀ = span(b_1, …, b_{k/2})`. -/
noncomputable def L0 : Finset F := R.spanRange 0 (R.k / 2)

/-- `L_R = span(b_{k/2+1}, …, b_{k/2+k̂+2})`. -/
noncomputable def LR : Finset F := R.spanRange (R.k / 2) (R.k / 2 + R.khat + 2)

/-- `L₁ = span(b_{k/2+1}, …, b_k) \ L_R`. -/
noncomputable def L1 : Finset F := R.spanRange (R.k / 2) R.k \ R.LR

/-- `L′₀ = L₀ + L_R`. -/
noncomputable def L0' : Finset F := Finset.image₂ (· + ·) R.L0 R.LR

/-- `L_β = span(L′₀, β)`. -/
noncomputable def Lβ (β : F) : Finset F := R.L0' ∪ R.L0'.image (β + ·)

/-- `q_{L₀}(z) = ∏_{α∈L₀} (z - α)`. -/
noncomputable def qL0 (z : F) : F := ∏ α ∈ R.L0, (z - α)

/-- `D_k̂(L) = ⋃_{β∈L₁} (L_β × {q_{L₀}(β)}) ∪ (L′₀ × q_{L₀}(L))`. -/
noncomputable def domain : Finset (F × F) :=
  (R.L1.biUnion fun β => R.Lβ β ×ˢ {R.qL0 β}) ∪ (R.L0' ×ˢ R.L.image R.qL0)

/-- The points of `D_k̂(L)`. -/
abbrev D : Type := {p : F × F // p ∈ R.domain}

/-- The row `K_x = {x} × {y : (x, y) ∈ D_k̂(L)}`. -/
noncomputable def row (x : F) : Finset R.D := Finset.univ.filter fun p => p.1.1 = x

/-- The column `K_y = {x : (x, y) ∈ D_k̂(L)} × {y}`. -/
noncomputable def col (y : F) : Finset R.D := Finset.univ.filter fun p => p.1.2 = y

/-- The curve `T = {(x, q_{L₀}(x)) : x ∈ L}`. -/
noncomputable def curve : Finset R.D := Finset.univ.filter fun p => p.1.1 ∈ R.L ∧ p.1.2 = R.qL0 p.1.1

/-- The rows `ℛ = {K_x : x ∈ L′₀}`. -/
noncomputable def rows : Finset (Finset R.D) := R.L0'.image R.row

/-- The columns `𝒦 = {K_y : y ∈ q_{L₀}(L₁)}`. -/
noncomputable def cols : Finset (Finset R.D) := (R.L1.image R.qL0).image R.col

theorem zero_mem_spanRange (lo hi : ℕ) : (0 : F) ∈ R.spanRange lo hi :=
  Finset.mem_image.2 ⟨∅, by simp, by simp⟩

theorem zero_mem_L0' (x : F) (hx : x ∈ R.L0') : (x, R.qL0 0) ∈ R.domain := by
  refine Finset.mem_union_right _ (Finset.mem_product.2 ⟨hx, ?_⟩)
  exact Finset.mem_image.2 ⟨0, R.zero_mem_spanRange _ _, rfl⟩

theorem self_mem_L0' (β : F) (hβ : β ∈ R.L1) : (β, R.qL0 β) ∈ R.domain := by
  refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨β, hβ, ?_⟩)
  refine Finset.mem_product.2 ⟨Finset.mem_union_right _ (Finset.mem_image.2 ⟨0, ?_, by simp⟩), by simp⟩
  exact Finset.mem_image₂.2 ⟨0, R.zero_mem_spanRange _ _, 0, R.zero_mem_spanRange _ _, by simp⟩

theorem zero_mem_0' : (0 : F) ∈ R.L0' :=
  Finset.mem_image₂.2 ⟨0, R.zero_mem_spanRange _ _, 0, R.zero_mem_spanRange _ _, by simp⟩

/-- The coded space `P_k̂(L) = D_k̂(L) ∪ ℛ ∪ 𝒦 ∪ {T}` (Definition 8.1, p.36), with each point as its singleton. -/
noncomputable def space : CodedSpace R.D where
  P := (Finset.univ.image fun p : R.D => ({p} : Finset R.D)) ∪ R.rows ∪ R.cols ∪ {R.curve}
  singleton_mem := fun x => by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl ⟨x, rfl⟩))
  nonempty_of_mem := by
    intro ρ hρ
    simp only [Finset.mem_union, Finset.mem_singleton] at hρ
    rcases hρ with ((hρ | hρ) | hρ) | rfl
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hρ
      exact Finset.singleton_nonempty p
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
      exact ⟨⟨(x, R.qL0 0), R.zero_mem_L0' x hx⟩, by simp [row]⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hρ
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨⟨(β, R.qL0 β), R.self_mem_L0' β hβ⟩, by simp [col]⟩
    · refine ⟨⟨(0, R.qL0 0), R.zero_mem_L0' 0 R.zero_mem_0'⟩, ?_⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, R.zero_mem_spanRange _ _, rfl⟩

/-- Evaluation of a univariate polynomial at `pt x` for `x ∈ ρ`, zero-padded. -/
noncomputable def evalPad {D : Type} (ρ : Finset D) (pt : D → F) : Polynomial F →ₗ[F] (D → F) where
  toFun p := fun x => if x ∈ ρ then p.eval (pt x) else 0
  map_add' p p' := by
    ext x; by_cases h : x ∈ ρ <;> simp [h]
  map_smul' c p := by
    ext x; by_cases h : x ∈ ρ <;> simp [h]

/-- The zero-padded evaluations on `ρ` of the polynomials of degree at most `d`, read at `pt`. -/
noncomputable def rsPad {D : Type} (ρ : Finset D) (pt : D → F) (d : ℕ) : Submodule F (D → F) :=
  (Polynomial.degreeLE F (d : ℕ)).map (evalPad ρ pt)

/-- All words on `ρ`, zero-padded (`F_p = 𝔽` at a point). -/
def fullPad {D : Type} (ρ : Finset D) : Submodule F (D → F) where
  carrier := {c | ∀ x, x ∉ ρ → c x = 0}
  add_mem' := by
    intro a b ha hb x hx
    simp [ha x hx, hb x hx]
  zero_mem' := by
    intro x _
    rfl
  smul_mem' := by
    intro c a ha x hx
    simp [ha x hx]

/-- The sheaf `F = F_{d_X, d_Y}(L)` of Definition 8.1, p.37: `F_p = 𝔽`, `F_{R_x} = RS[𝔽, R_x, d_Y]` as polynomials in `y`,
`F_{K_y} = RS[𝔽, K_y, d_X]` as polynomials in `x`, and `F_T = {c : (c(x, q_{L₀}(x)))_{x∈L} ∈ RS[𝔽, L, d_X + d_Y · |L₀|]}`. -/
noncomputable def codes (dX dY : ℕ) : LocalCodes F R.D where
  code ρ :=
    if ρ = R.curve then rsPad ρ (fun p => p.1.1) (dX + dY * R.L0.card)
    else if ρ ∈ R.rows then rsPad ρ (fun p => p.1.2) dY
    else if ρ ∈ R.cols then rsPad ρ (fun p => p.1.1) dX
    else fullPad ρ

/-- The distribution on the cover `ℛ ∪ 𝒦` (App. C, p.49): a uniform row with probability `1/2` and a uniform column with
probability `1/2`. -/
noncomputable def rowColLaw : PMF (Finset R.D) :=
  (PMF.uniformOfFintype Bool).bind fun c =>
    if c then uniformOn ∅ R.rows else uniformOn ∅ R.cols

/-- The conditions of Definition 8.1 (p.36), for `𝔽` of size `2^l`: `k` even, `k < l`, `k/2 + k̂ + 2 < k`, the `b_j` are
`𝔽₂`-linearly independent (distinct subsets have distinct sums), and `d_X + 1 = 2^{k̂+k/2}`. -/
structure Valid [Fintype F] (dX : ℕ) : Prop where
  card : Fintype.card F = 2 ^ R.l
  even : Even R.k
  k_lt : R.k < R.l
  khat_lt : R.k / 2 + R.khat + 2 < R.k
  indep : Function.Injective fun T : Finset (Fin R.k) => ∑ j ∈ T, R.b j
  dX_eq : dX + 1 = 2 ^ (R.khat + R.k / 2)

end RMParams

end ZKSheafPCP


