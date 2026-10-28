-- Prove2me | Definitions.Def_WilliamsonShmoys_TriangularMap
-- name    : WilliamsonShmoys_TriangularMap
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-25T22:15:56.425769+00:00
-- url     : https://prove2.me/theorems/6f5c527a-99c8-4dde-8363-42d27e07804f
-- title:
--   Finite oriented triangular maps and complementary dual graphs
-- statement:
--   A triangular map records oriented face corners, a bijection from face sides to graph darts, distinct corners, vertex coverage, primal connectivity, and one cyclic rotation at each vertex. Advancing after reversing a dart implements that vertex rotation. The bundle assumes neither Euler characteristic nor decomposition properties. Its complementary dual joins distinct faces across sides absent from a specified primal graph, retaining existential side witnesses so parallel dual sides are handled correctly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

/-- An oriented finite triangular map. The dart equivalence accounts for every
oriented edge exactly once. Vertex rotations are single cycles. No Euler
characteristic or tree-decomposition property is assumed. -/
structure WilliamsonShmoys.TriangularMap
    {V : Type} [Fintype V] (H : SimpleGraph V)
    (F : Type) [Fintype F] where
  corner : F → Fin 3 → V
  dart : (F × Fin 3) ≃ H.Dart
  dart_tail : ∀ f i, (dart (f, i)).fst = corner f i
  dart_head : ∀ f i, (dart (f, i)).snd = corner f (i + 1)
  corners_distinct : ∀ f, Function.Injective (corner f)
  vertex_covered : ∀ v, ∃ f i, corner f i = v
  connected : H.Connected
  rotation_transitive : ∀ d e : H.Dart, d.fst = e.fst →
    ∃ k : Nat,
      (fun a : H.Dart =>
        dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e

/-- Faces are adjacent if some common side is absent from the primal graph R.
This is the simple graph underlying the complementary dual multigraph. -/
def WilliamsonShmoys.TriangularMap.cotree
    {V F : Type} [Fintype V] [Fintype F]
    {H : SimpleGraph V} (M : WilliamsonShmoys.TriangularMap H F)
    (R : SimpleGraph V) : SimpleGraph F where
  Adj f g := f ≠ g ∧ ∃ d : H.Dart,
    ¬ R.Adj d.fst d.snd ∧
    (M.dart.symm d).1 = f ∧ (M.dart.symm d.symm).1 = g
  symm.symm := by
    rintro f g ⟨hne, d, hd, hf, hg⟩
    refine ⟨hne.symm, d.symm, ?_, hg, ?_⟩
    · exact fun h => hd h.symm
    · simpa only [SimpleGraph.Dart.symm_symm] using hf
  loopless.irrefl := by
    intro f h
    exact h.1 rfl


