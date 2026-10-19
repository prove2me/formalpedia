-- Prove2me | Definitions.Def_QAlgorithms_Defs_TensorCode
-- name    : QAlgorithms_Defs_TensorCode
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:54:29.851803+00:00
-- url     : https://prove2.me/theorems/b1476814-ee93-4c82-a965-9f4d62432665
-- title:
--   Binary tensor codes, dual tensor codes, robustness, Cayley graphs (shared definition layer)
-- statement:
--   # Binary tensor codes, dual tensor codes, robustness, Cayley graphs (shared definition layer)
--
--   * A. Leverrier, G. Zémor, *Quantum Tanner codes* (arXiv:2202.13641v3), cited "LZ p.N" (PDF pages).
--   * A. Leverrier, G. Zémor, *Efficient decoding up to a constant fraction of the code length for
--     asymptotically good quantum codes* (arXiv:2208.05537v3), cited "LZ-dec p.N" (PDF pages).
--
--   Conventions. A vector of `F₂^{A×B}` is a function `x : α × β → ZMod 2` (first index `a` = row,
--   second index `b` = column; the column labelled `b` is `fun a => x (a, b)`). A linear code on a
--   finite coordinate type `ι` is a `Submodule (ZMod 2) (ι → ZMod 2)`; the Hamming weight `|x|` is
--   Mathlib's `hammingNorm x`.
--   -/
--
--   namespace QAlgorithms
--
--   /-- LZ p.15, LZ-dec p.4 (eq. (1)): the column code `C_A ⊗ F₂^B`, the words of `F₂^{A×B}` all of
--   whose columns `(x_{ab})_{a ∈ A}` are codewords of `C_A`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TensorCode.lean

import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
/-!
# Binary tensor codes, dual tensor codes, robustness, Cayley graphs (shared definition layer)

* A. Leverrier, G. Zémor, *Quantum Tanner codes* (arXiv:2202.13641v3), cited "LZ p.N" (PDF pages).
* A. Leverrier, G. Zémor, *Efficient decoding up to a constant fraction of the code length for
  asymptotically good quantum codes* (arXiv:2208.05537v3), cited "LZ-dec p.N" (PDF pages).

Conventions. A vector of `F₂^{A×B}` is a function `x : α × β → ZMod 2` (first index `a` = row,
second index `b` = column; the column labelled `b` is `fun a => x (a, b)`). A linear code on a
finite coordinate type `ι` is a `Submodule (ZMod 2) (ι → ZMod 2)`; the Hamming weight `|x|` is
Mathlib's `hammingNorm x`.
-/

namespace QAlgorithms

/-- LZ p.15, LZ-dec p.4 (eq. (1)): the column code `C_A ⊗ F₂^B`, the words of `F₂^{A×B}` all of
whose columns `(x_{ab})_{a ∈ A}` are codewords of `C_A`. -/
def columnCode {α : Type*} (CA : Submodule (ZMod 2) (α → ZMod 2)) (β : Type*) :
    Submodule (ZMod 2) (α × β → ZMod 2) where
  carrier := {x | ∀ b, (fun a => x (a, b)) ∈ CA}
  add_mem' := by
    intro x y hx hy b
    exact CA.add_mem (hx b) (hy b)
  zero_mem' := by
    intro b
    exact CA.zero_mem
  smul_mem' := by
    intro c x hx b
    exact CA.smul_mem c (hx b)

/-- LZ p.15, LZ-dec p.4: the row code `F₂^A ⊗ C_B`, the words all of whose rows
`(x_{ab})_{b ∈ B}` are codewords of `C_B`. -/
def rowCode (α : Type*) {β : Type*} (CB : Submodule (ZMod 2) (β → ZMod 2)) :
    Submodule (ZMod 2) (α × β → ZMod 2) where
  carrier := {x | ∀ a, (fun b => x (a, b)) ∈ CB}
  add_mem' := by
    intro x y hx hy a
    exact CB.add_mem (hx a) (hy a)
  zero_mem' := by
    intro a
    exact CB.zero_mem
  smul_mem' := by
    intro c x hx a
    exact CB.smul_mem c (hx a)

/-- LZ p.15, LZ-dec pp.4, 11: the dual tensor code `C_A ⊗ F₂^B + F₂^A ⊗ C_B` (which equals
`(C_A^⊥ ⊗ C_B^⊥)^⊥`, a fact of the sources, not used as the definition). -/
def dualTensorCode {α β : Type*} (CA : Submodule (ZMod 2) (α → ZMod 2))
    (CB : Submodule (ZMod 2) (β → ZMod 2)) : Submodule (ZMod 2) (α × β → ZMod 2) :=
  columnCode CA β ⊔ rowCode α CB

/-- LZ p.15 ("`C_A ⊗ C_B = C_A ⊗ F₂^B ∩ F₂^A ⊗ C_B`"), LZ-dec p.11: the tensor code
`C_A ⊗ C_B`, every column in `C_A` and every row in `C_B`. -/
def tensorCode {α β : Type*} (CA : Submodule (ZMod 2) (α → ZMod 2))
    (CB : Submodule (ZMod 2) (β → ZMod 2)) : Submodule (ZMod 2) (α × β → ZMod 2) :=
  columnCode CA β ⊓ rowCode α CB

/-- LZ-dec p.4 (after eq. (1)): `‖c‖`, the number of non-zero columns of `c ∈ F₂^{A×B}`. -/
def nonzeroCols {α β : Type*} [Fintype α] [Fintype β] (x : α × β → ZMod 2) : ℕ :=
  (Finset.univ.filter fun b : β => ∃ a, x (a, b) ≠ 0).card

/-- LZ-dec p.4: `‖r‖`, the number of non-zero rows of `r ∈ F₂^{A×B}`. -/
def nonzeroRows {α β : Type*} [Fintype α] [Fintype β] (x : α × β → ZMod 2) : ℕ :=
  (Finset.univ.filter fun a : α => ∃ b, x (a, b) ≠ 0).card

/-- LZ-dec pp.4, 8: the binary dual code `C^⊥ = {y | c · y = 0 for all c ∈ C}` on an arbitrary
finite coordinate type (the frozen `binDual` is the same object on `Fin n` only). -/
def codeDual {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {y | ∀ c ∈ C, c ⬝ᵥ y = 0}
  add_mem' := by
    intro x y hx hy c hc
    rw [dotProduct_add, hx c hc, hy c hc, add_zero]
  zero_mem' := by
    intro c _
    exact dotProduct_zero c
  smul_mem' := by
    intro a x hx c hc
    rw [dotProduct_smul, hx c hc, smul_zero]

/-- LZ p.15 (Definition 5, `d_A`, `d_B`): the minimum distance of a binary code, the least
Hamming weight of a non-zero codeword, valued in `ℕ∞` (`⊤` for the zero code, `d(0) = ∞`;
no junk value `0`). -/
noncomputable def minDistCode {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ∞ :=
  ⨅ x ∈ C, ⨅ (_ : x ≠ 0), (hammingNorm x : ℕ∞)

/-- LZ p.8, LZ-dec p.4: "`C` has minimum distance `⩾ d`": every non-zero codeword has weight
`⩾ d` (the zero code satisfies it vacuously). -/
def HasMinDistAtLeast {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (ι → ZMod 2)) (d : ℝ) :
    Prop :=
  ∀ x ∈ C, x ≠ 0 → d ≤ (hammingNorm x : ℝ)

/-- LZ p.16: the punctured code `C_{A'}`, the subvectors `(c_a)_{a ∈ A'}` of the codewords of `C`. -/
def puncture {α : Type*} (C : Submodule (ZMod 2) (α → ZMod 2)) (S : Finset α) :
    Submodule (ZMod 2) (S → ZMod 2) :=
  C.map (LinearMap.funLeft (ZMod 2) (ZMod 2) (Subtype.val : S → α))

/-- LZ p.15, Definition 5: the dual tensor code `C_A ⊗ F₂^B + F₂^A ⊗ C_B` is `w`-robust: every
codeword `x` with `|x| ⩽ w` admits `A' ⊆ A`, `B' ⊆ B` with `|A'| ⩽ |x|/d_B`, `|B'| ⩽ |x|/d_A` and
`x_{ab} = 0` whenever `a ∉ A'` and `b ∉ B'`. The divisions are cleared in `ℕ∞`
(`|A'| · d_B ⩽ |x|`), so a zero code (`d = ⊤`) forces the corresponding set to be empty, as
`|x|/∞ = 0` does. The page's range `0 ⩽ w ⩽ Δ²` is a range for `w`, not part of the property. -/
def IsWRobust {α β : Type*} [Fintype α] [Fintype β] (CA : Submodule (ZMod 2) (α → ZMod 2))
    (CB : Submodule (ZMod 2) (β → ZMod 2)) (w : ℝ) : Prop :=
  ∀ x ∈ dualTensorCode CA CB, (hammingNorm x : ℝ) ≤ w →
    ∃ (A' : Finset α) (B' : Finset β),
      (A'.card : ℕ∞) * minDistCode CB ≤ (hammingNorm x : ℕ∞) ∧
      (B'.card : ℕ∞) * minDistCode CA ≤ (hammingNorm x : ℕ∞) ∧
      ∀ a b, a ∉ A' → b ∉ B' → x (a, b) = 0

/-- LZ p.16, Definition 8: the dual tensor code is `w`-robust with `p`-resistance to puncturing:
for all `A' ⊆ A`, `B' ⊆ B` with `|A'| = |B'| = Δ − w'`, `w' ⩽ p`, the dual tensor code of the
punctured codes `(C_A)_{A'}`, `(C_B)_{B'}` is `w`-robust. Here `Δ = |A|` (the statements give
`|A| = |B| = Δ`); `w' := Δ − |A'|` is exact in `ℕ` since `|A'| ⩽ |A|`. -/
def IsRobustResistant {α β : Type*} [Fintype α] [Fintype β] (CA : Submodule (ZMod 2) (α → ZMod 2))
    (CB : Submodule (ZMod 2) (β → ZMod 2)) (w p : ℝ) : Prop :=
  ∀ (A' : Finset α) (B' : Finset β), A'.card = B'.card →
    ((Fintype.card α - A'.card : ℕ) : ℝ) ≤ p → IsWRobust (puncture CA A') (puncture CB B') w

/-- LZ-dec p.4 (eq. (1)), p.12: `κ`-robustness (`κ`-product-expansion) of the dual tensor code:
every `x ∈ C_A ⊗ F₂^B + F₂^A ⊗ C_B` has a decomposition `x = c + r`, `c` in the column code and
`r` in the row code, with `|x| ⩾ κΔ(‖c‖ + ‖r‖)`, `Δ` the common length `|A| = |B|`. -/
def IsProductExpanding {α β : Type*} [Fintype α] [Fintype β] (CA : Submodule (ZMod 2) (α → ZMod 2))
    (CB : Submodule (ZMod 2) (β → ZMod 2)) (Δ : ℕ) (κ : ℝ) : Prop :=
  ∀ x ∈ dualTensorCode CA CB, ∃ c ∈ columnCode CA β, ∃ r ∈ rowCode α CB,
    x = c + r ∧ κ * Δ * ((nonzeroCols c + nonzeroRows r : ℕ) : ℝ) ≤ (hammingNorm x : ℝ)

/-- LZ p.11, LZ-dec pp.7, 10: the adjacency matrix of the left Cayley graph `Cay(G, A)` (edges
`g — ag`, `a ∈ A`), counted with multiplicity: entry `(g, g')` is `#{a ∈ A | g' = a g}`
(symmetric when `A = A⁻¹`). -/
def leftCayleyAdj {G : Type*} [Group G] [DecidableEq G] (A : Finset G) : Matrix G G ℝ :=
  Matrix.of fun g g' => ((A.filter fun a => g' = a * g).card : ℝ)

/-- LZ p.11, LZ-dec p.10: the adjacency matrix of the right Cayley graph `Cay(G, B)` (edges
`g — gb`): entry `(g, g')` is `#{b ∈ B | g' = g b}`. -/
def rightCayleyAdj {G : Type*} [Group G] [DecidableEq G] (B : Finset G) : Matrix G G ℝ :=
  Matrix.of fun g g' => ((B.filter fun b => g' = g * b).card : ℝ)

/-- LZ p.12 (Lemma 4, the graphs `G_A`, `G_B`): the bipartite double cover of the multigraph with
adjacency matrix `M`, on `V × {0, 1}` with edges between `(v, i)` and `(v', 1 − i)` of
multiplicity `M v v'`; for `M = leftCayleyAdj A` the edges are `(g, 0) — (ag, 1)`. -/
def bipartiteDoubleCover {V : Type*} (M : Matrix V V ℝ) : Matrix (V × Bool) (V × Bool) ℝ :=
  Matrix.of fun p q => if p.2 ≠ q.2 then M p.1 q.1 else 0

/-- LZ p.11, LZ-dec p.7: the multigraph with adjacency matrix `M` is connected (loops and
multiplicities are irrelevant; `Connected` includes non-emptiness of the vertex set). -/
def adjConnected {V : Type*} (M : Matrix V V ℝ) : Prop :=
  (SimpleGraph.fromRel fun u v => M u v ≠ 0).Connected

/-- LZ §3.1 p.11, LZ-dec p.7: a connected `Δ`-regular graph is Ramanujan if
`λ(G) = max{|λ_i| : λ_i ≠ ±Δ} ⩽ 2√(Δ − 1)`. Stated for a symmetric adjacency matrix `M`
(eigenvalues with multiplicity, the frozen `ascEigenvalues`); `IsHermitian` is part of the
definition so that the junk value `0` of `ascEigenvalues` on a non-symmetric matrix cannot
satisfy the bound. Regularity is a separate hypothesis of the statements. -/
def IsRamanujanAdj {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) (Δ : ℕ) : Prop :=
  M.IsHermitian ∧ adjConnected M ∧
    ∀ k, |ascEigenvalues M k| ≠ (Δ : ℝ) → |ascEigenvalues M k| ≤ 2 * Real.sqrt ((Δ : ℝ) - 1)

/-! ### Sanity tests -/

example {α β : Type*} (x : α × β → ZMod 2) : x ∈ columnCode (⊤ : Submodule (ZMod 2) (α → ZMod 2)) β :=
  fun _ => Submodule.mem_top

example {α β : Type*} (CA : Submodule (ZMod 2) (α → ZMod 2)) (CB : Submodule (ZMod 2) (β → ZMod 2))
    (x : α × β → ZMod 2) (hx : x ∈ columnCode CA β) : x ∈ dualTensorCode CA CB :=
  Submodule.mem_sup_left hx

example {α β : Type*} [Fintype α] [Fintype β] : nonzeroCols (0 : α × β → ZMod 2) = 0 ∧
    nonzeroRows (0 : α × β → ZMod 2) = 0 := by
  simp [nonzeroCols, nonzeroRows]

example : nonzeroCols (fun p : Fin 2 × Fin 3 => if p.2 = 1 then (1 : ZMod 2) else 0) = 1 := by
  decide

example {ι : Type*} [Fintype ι] : minDistCode (⊥ : Submodule (ZMod 2) (ι → ZMod 2)) = ⊤ := by
  simp [minDistCode]

example {α β : Type*} [Fintype α] [Fintype β] (CA : Submodule (ZMod 2) (α → ZMod 2))
    (CB : Submodule (ZMod 2) (β → ZMod 2)) : IsWRobust CA CB 0 := by
  intro x _ hx
  have h0 : hammingNorm x = 0 := by
    have : (hammingNorm x : ℝ) = 0 := le_antisymm hx (Nat.cast_nonneg _)
    exact_mod_cast this
  have hx0 : x = 0 := hammingNorm_eq_zero.1 h0
  refine ⟨∅, ∅, by simp, by simp, fun a b _ _ => by simp [hx0]⟩

example {G : Type*} [Group G] [DecidableEq G] : leftCayleyAdj ({1} : Finset G) = 1 := by
  ext g g'
  by_cases h : g' = g
  · subst h; simp [leftCayleyAdj, Finset.filter_singleton]
  · simp [leftCayleyAdj, Matrix.one_apply, h, Ne.symm h, Finset.filter_singleton]

example {V : Type*} (M : Matrix V V ℝ) (v : V) (b : Bool) :
    bipartiteDoubleCover M (v, b) (v, b) = 0 := by
  simp [bipartiteDoubleCover]

end QAlgorithms


