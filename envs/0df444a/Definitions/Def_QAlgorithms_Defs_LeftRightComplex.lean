-- Prove2me | Definitions.Def_QAlgorithms_Defs_LeftRightComplex
-- name    : QAlgorithms_Defs_LeftRightComplex
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:55:25.531018+00:00
-- url     : https://prove2.me/theorems/8adc57b6-7820-4d45-9f18-83d0c7b763d4
-- title:
--   The bipartite left-right Cayley complex and the Tanner code `C₁` (shared definition layer)
-- statement:
--   # The bipartite left-right Cayley complex and the Tanner code `C₁` (shared definition layer)
--
--   A. Leverrier, G. Zémor, *Quantum Tanner codes* (arXiv:2202.13641v3), cited "LZ p.N" (PDF pages),
--   §§3.2, 4.
--
--   Conventions. `G` is a finite group, `A, B ⊆ G` the generating sets. The vertex set is
--   `V = G × {0, 1}`, `V₀ = G × {false}`, `V₁ = G × {true}`. A square is the 4-subset
--   `{(g,0), (ag,1), (gb,1), (agb,0)}` of `V` (LZ p.12), so that the squares obtained from
--   `(g, a, b)` and `(agb, a⁻¹, b⁻¹)` coincide, as in the source. `F₂^Q` is
--   `lzSquares A B → ZMod 2`.
--   -/
--
--   namespace QAlgorithms
--
--   variable {G : Type*} [Group G] [DecidableEq G]
--
--   /-- LZ p.11, condition (1) (Total No-Conjugacy): `ag ≠ gb` for all `a ∈ A`, `b ∈ B`, `g ∈ G`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\LeftRightComplex.lean

import Definitions.Def_QAlgorithms_Defs_TensorCode
/-!
# The bipartite left-right Cayley complex and the Tanner code `C₁` (shared definition layer)

A. Leverrier, G. Zémor, *Quantum Tanner codes* (arXiv:2202.13641v3), cited "LZ p.N" (PDF pages),
§§3.2, 4.

Conventions. `G` is a finite group, `A, B ⊆ G` the generating sets. The vertex set is
`V = G × {0, 1}`, `V₀ = G × {false}`, `V₁ = G × {true}`. A square is the 4-subset
`{(g,0), (ag,1), (gb,1), (agb,0)}` of `V` (LZ p.12), so that the squares obtained from
`(g, a, b)` and `(agb, a⁻¹, b⁻¹)` coincide, as in the source. `F₂^Q` is
`lzSquares A B → ZMod 2`.
-/

namespace QAlgorithms

variable {G : Type*} [Group G] [DecidableEq G]

/-- LZ p.11, condition (1) (Total No-Conjugacy): `ag ≠ gb` for all `a ∈ A`, `b ∈ B`, `g ∈ G`. -/
def IsTNC (A B : Finset G) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ g : G, a * g ≠ g * b

/-- LZ pp.12, 17: the square `{v, av, vb, avb}` of the left-right Cayley complex through the
vertex `v = (g, i)`: `av = (ag, 1 − i)`, `vb = (gb, 1 − i)`, `avb = (agb, i)`. -/
def lzSquare (v : G × Bool) (a b : G) : Finset (G × Bool) :=
  {v, (a * v.1, !v.2), (v.1 * b, !v.2), (a * v.1 * b, v.2)}

/-- LZ p.12: the set `Q` of squares `{(g,0), (ag,1), (gb,1), (agb,0)}`, `g ∈ G`, `a ∈ A`,
`b ∈ B`, as 4-subsets of `V` (`|Q| = Δ²|G|/2` under TNC with `A = A⁻¹`, `B = B⁻¹`). -/
def lzSquares [Fintype G] (A B : Finset G) : Finset (Finset (G × Bool)) :=
  (Finset.univ ×ˢ A ×ˢ B).image fun t => lzSquare (t.1, false) t.2.1 t.2.2

/-- LZ p.17: the local view `x_v` of `x ∈ F₂^Q` at the vertex `v`, read as an `A × B` array through
`φ_v : (a, b) ↦ {v, av, vb, avb}`. With `A = A⁻¹`, `B = B⁻¹` every `φ_v(a, b)` is a square, so the
`else` branch (value `0`) is never used for the source's complexes. -/
def lzLocalView [Fintype G] {A B : Finset G} (x : lzSquares A B → ZMod 2) (v : G × Bool) :
    A × B → ZMod 2 :=
  fun ab => if h : lzSquare v ab.1 ab.2 ∈ lzSquares A B then x ⟨_, h⟩ else 0

/-- LZ p.18, eq. (4): the Tanner code `C₁ = T(G₁^□, C₁^⊥)`: every local view at a vertex of `V₁` is
a codeword of the dual tensor code `C_A ⊗ F₂^B + F₂^A ⊗ C_B`. -/
def lzTannerCode1 [Fintype G] (A B : Finset G) (CA : Submodule (ZMod 2) (A → ZMod 2))
    (CB : Submodule (ZMod 2) (B → ZMod 2)) : Submodule (ZMod 2) (lzSquares A B → ZMod 2) where
  carrier := {x | ∀ g : G, lzLocalView x (g, true) ∈ dualTensorCode CA CB}
  add_mem' := by
    intro x y hx hy g
    have h : lzLocalView (x + y) (g, true) = lzLocalView x (g, true) + lzLocalView y (g, true) := by
      funext ab
      simp only [lzLocalView, Pi.add_apply]
      split_ifs <;> simp
    rw [h]
    exact add_mem (hx g) (hy g)
  zero_mem' := by
    intro g
    have h : lzLocalView (0 : lzSquares A B → ZMod 2) (g, true) = 0 := by
      funext ab
      simp [lzLocalView]
    rw [h]
    exact zero_mem _
  smul_mem' := by
    intro c x hx g
    have h : lzLocalView (c • x) (g, true) = c • lzLocalView x (g, true) := by
      funext ab
      simp only [lzLocalView, Pi.smul_apply]
      split_ifs <;> simp
    rw [h]
    exact Submodule.smul_mem _ c (hx g)

/-- LZ p.8 (Theorem 1), p.22: the vector `y ∈ F₂^Q` equal to `c ∘ φ_v⁻¹` on the
`Q`-neighbourhood `Q(v)` and `0` elsewhere (under TNC, `(a, b) ↦ {v, av, vb, avb}` is injective,
so the chosen preimage is the unique one). -/
noncomputable def lzExtend [Fintype G] {A B : Finset G} (v : G × Bool) (c : A × B → ZMod 2) :
    lzSquares A B → ZMod 2 :=
  open Classical in
  fun q => if h : ∃ ab : A × B, lzSquare v ab.1 ab.2 = q.1 then c h.choose else 0

/-! ### Sanity tests -/

example (g : G) : lzSquare ((g, false) : G × Bool) 1 1 = {(g, false), (g, true)} := by
  ext p
  simp [lzSquare]
  tauto

example [Fintype G] (A B : Finset G) (g : G) (a : A) (b : B) :
    lzSquare ((g, false) : G × Bool) a b ∈ lzSquares A B := by
  simp only [lzSquares, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
  exact ⟨(g, a, b), ⟨a.2, b.2⟩, rfl⟩

example [Fintype G] (A B : Finset G) (CA : Submodule (ZMod 2) (A → ZMod 2))
    (CB : Submodule (ZMod 2) (B → ZMod 2)) : (0 : lzSquares A B → ZMod 2) ∈ lzTannerCode1 A B CA CB :=
  zero_mem _

example [Fintype G] {A B : Finset G} (v : G × Bool) (q : lzSquares A B) :
    lzExtend v (0 : A × B → ZMod 2) q = 0 := by
  simp [lzExtend]

end QAlgorithms


