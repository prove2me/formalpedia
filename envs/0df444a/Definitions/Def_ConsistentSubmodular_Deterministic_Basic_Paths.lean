-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Paths
-- name    : ConsistentSubmodular_Deterministic_Basic_Paths
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:02.960275+00:00
-- url     : https://prove2.me/theorems/75b42142-5586-481b-b1a3-a2e076f8e629
-- title:
--   Polygonal paths in the simplex: constant, segment, reverse, append; monotonicity of certificates in the segment budget
-- statement:
--   A polygonal path $\gamma$ in $\mathbb R^{m+1}$ (`PolygonalPath m`) has a number of pieces $\ell$ and nodes $\gamma_0,\dots,\gamma_\ell$ (`pieces`, `node`); its $i$-th piece is the segment $x\mapsto \mathrm{mix}(\gamma_{i},\gamma_{i+1},x)$, $x\in[0,1]$, with $0\le i<\ell$. The predicate $\gamma.\mathrm{Along}\,\Phi$ means that $\Phi$ holds at every node and at every point of every piece. This file builds paths and the operations on them.
--
--   - `PolygonalPath.constant p`: the path with $0$ pieces and the single node $p$.
--   - `PolygonalPath.segment p q`: the path with $1$ piece and nodes $p,q$.
--   - `PolygonalPath.reverse γ`: the path with the same number of pieces and nodes $\gamma_{\ell-i}$ (`Fin.rev`), so it runs from the terminal node of $\gamma$ to its initial node.
--   - `PolygonalPath.append γ δ`: the concatenation, with $\ell_\gamma+\ell_\delta$ pieces. Its node $i$ is $\gamma_i$ for $i\le\ell_\gamma$ and $\delta_{\,i-\ell_\gamma}$ otherwise. It is the path through $\gamma$ followed by $\delta$ when the last node of $\gamma$ equals the first node of $\delta$; in that case the node at $i=\ell_\gamma$ is the shared point.
--   - `WindowInstance.Certificate.mono`: an $(\alpha,L)$-certificate for a window instance $W$ is also an $(\alpha,L')$-certificate for every $L'\ge L$. The fields are unchanged and only the segment inequality $\ell_{\text{entry}}+\ell_{\text{exit}}\le L\le L'$ is weakened.
--
--   The file also proves the basic facts: the number of pieces of the constant, segment and append paths, the initial and terminal nodes of each construction (for `append` the terminal node is that of $\delta$, given the join condition), the formulas for the nodes of `append` on each side of the join, and that `Along` is monotone in the property and compatible with conjunction.
--
--   These operations assemble the entry and exit paths of clairvoyant certificates (Definition 3.1) from vertex-to-vertex segments, and bound the total number of segments.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/Paths.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Simplex

noncomputable section

namespace ConsistentSubmodular

variable {m : ℕ}

namespace PolygonalPath

def constant (p : Point m) : PolygonalPath m where
  pieces := 0
  node := fun _ => p

def segment (p q : Point m) : PolygonalPath m where
  pieces := 1
  node := fun j => if j = 0 then p else q

def reverse (γ : PolygonalPath m) : PolygonalPath m where
  pieces := γ.pieces
  node := fun i => γ.node i.rev

@[simp] theorem reverse_pieces (γ : PolygonalPath m) : γ.reverse.pieces = γ.pieces := rfl

@[simp] theorem reverse_initial (γ : PolygonalPath m) :
    γ.reverse.node 0 = γ.node (Fin.last γ.pieces) := by
  change γ.node (Fin.rev (0 : Fin (γ.pieces + 1))) = γ.node (Fin.last γ.pieces)
  rw [Fin.rev_zero]

@[simp] theorem reverse_terminal (γ : PolygonalPath m) :
    γ.reverse.node (Fin.last γ.reverse.pieces) = γ.node 0 := by
  simp [reverse]

@[simp] theorem constant_pieces (p : Point m) : (constant p).pieces = 0 := rfl

@[simp] theorem constant_node (p : Point m) (j : Fin ((constant p).pieces + 1)) :
    (constant p).node j = p := rfl

@[simp] theorem segment_pieces (p q : Point m) : (segment p q).pieces = 1 := rfl

@[simp] theorem segment_initial (p q : Point m) : (segment p q).node 0 = p := by
  rfl

@[simp] theorem segment_terminal (p q : Point m) :
    (segment p q).node (Fin.last 1) = q := by
  simp [segment]

@[simp] theorem segment_one (p q : Point m) : (segment p q).node 1 = q := rfl

def append (γ δ : PolygonalPath m) : PolygonalPath m where
  pieces := γ.pieces + δ.pieces
  node := fun i => if h : i.val ≤ γ.pieces then
    γ.node ⟨i.val, by omega⟩ else δ.node ⟨i.val - γ.pieces, by omega⟩

@[simp] theorem append_pieces (γ δ : PolygonalPath m) :
    (append γ δ).pieces = γ.pieces + δ.pieces := rfl

theorem append_node_left (γ δ : PolygonalPath m)
    (i : Fin ((append γ δ).pieces + 1)) (hi : i.val ≤ γ.pieces) :
    (append γ δ).node i = γ.node ⟨i.val, by omega⟩ := by
  simp [append, hi]

theorem append_node_right (γ δ : PolygonalPath m)
    (hjoin : γ.node (Fin.last γ.pieces) = δ.node 0)
    (i : Fin ((append γ δ).pieces + 1)) (hi : γ.pieces ≤ i.val) :
    (append γ δ).node i = δ.node ⟨i.val - γ.pieces, by
      have := i.isLt
      simp only [append_pieces] at this
      omega⟩ := by
  unfold append
  dsimp only
  split_ifs with h
  · have heq : i.val = γ.pieces := by omega
    have hleft : (⟨i.val, by omega⟩ : Fin (γ.pieces + 1)) = Fin.last γ.pieces := by
      apply Fin.ext
      exact heq
    have hright : (⟨i.val - γ.pieces, by omega⟩ : Fin (δ.pieces + 1)) = 0 := by
      apply Fin.ext
      simp [heq]
    rw [hleft, hright, hjoin]
  · rfl

@[simp] theorem append_initial (γ δ : PolygonalPath m) :
    (append γ δ).node 0 = γ.node 0 := by
  rw [append_node_left γ δ 0 (by simp)]
  rfl

theorem append_terminal (γ δ : PolygonalPath m)
    (hjoin : γ.node (Fin.last γ.pieces) = δ.node 0) :
    (append γ δ).node (Fin.last (append γ δ).pieces) = δ.node (Fin.last δ.pieces) := by
  rw [append_node_right γ δ hjoin _ (by simp)]
  congr 1
  apply Fin.ext
  simp

theorem Along.mono {γ : PolygonalPath m} {Φ Ψ : Point m → Prop} (h : γ.Along Φ)
    (hΦΨ : ∀ q, Φ q → Ψ q) : γ.Along Ψ :=
  ⟨fun i => hΦΨ _ (h.1 i), fun i x hx hx1 => hΦΨ _ (h.2 i x hx hx1)⟩

theorem Along.and {γ : PolygonalPath m} {Φ Ψ : Point m → Prop} (hΦ : γ.Along Φ)
    (hΨ : γ.Along Ψ) : γ.Along (fun q => Φ q ∧ Ψ q) :=
  ⟨fun i => ⟨hΦ.1 i, hΨ.1 i⟩, fun i x hx hx1 => ⟨hΦ.2 i x hx hx1, hΨ.2 i x hx hx1⟩⟩

end PolygonalPath

namespace WindowInstance

variable {n : ℕ} {W : WindowInstance n}

namespace Certificate

/-- A certificate stays one when the segment budget grows. -/
def mono {α : ℝ} {L L' : ℕ} (C : W.Certificate α L) (hL : L ≤ L') : W.Certificate α L' :=
  { C with segments := C.segments.trans hL }

end Certificate

end WindowInstance

end ConsistentSubmodular

end


