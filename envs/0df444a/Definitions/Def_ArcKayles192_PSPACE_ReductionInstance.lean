-- Prove2me | Definitions.Def_ArcKayles192_PSPACE_ReductionInstance
-- name    : ArcKayles192_PSPACE_ReductionInstance
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:53:24.159023+00:00
-- url     : https://prove2.me/theorems/22b19879-fe85-46da-91d6-ff16d9734377
-- title:
--   The explicit adjacency-matrix instance $G_\varphi$, odd-clause padding, and the full reduction map
-- statement:
--   For a Pos CNF instance $\varphi$ with $n$ variables and $m$ clauses, this module turns the construction $G_\varphi$ into an actual `GraphInstance`, hence into the input format of ARC KAYLES.
--
--   The $N=2+2m+2R+n+2K$ vertices are numbered in the order $s,t,A,B,V,T,F,Y,Z$, and the adjacency bit at $(i,j)$ is the adjacency relation of $G_\varphi$ after translating matrix indices back to vertices. The resulting matrix is symmetric and irreflexive.
--
--   When $m>0$ is even, `oddPad` duplicates $C_1$; otherwise it leaves the formula alone. Thus the padded formula has an odd number of clauses whenever $m>0$, exactly as required by Claims 7–10. The full map `reductionInstance` sends $\varphi$ to the matrix of $G_{\mathrm{oddPad}(\varphi)}$. The paper does not discuss $m=0$, where duplication is impossible; since the empty conjunction is a win for True, `reductionInstance` uses the one-edge graph $K_2$, a first-player win in Arc Kayles.
--
--   **Formalization Note.** The explicit numbering `vtxFin` and equivalence `vtxEquiv` make the vertex order reusable by the polynomial-time construction lemma and avoid relying on a noncanonical `Fintype.equivFin`. Indices are 0-based, consistently with `Def_ArcKayles192_PSPACE_Construction`.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, pp.5–6, proof of Theorem 1: odd-m padding and Construction (vertex and edge sets, K, R, graph size). The m=0 and m even with m>0 case split makes the paper's clause-duplication instruction total.

import Definitions.Def_ArcKayles192_PSPACE_Construction
import Definitions.Def_ArcKayles192_PSPACE_Game

namespace ArcKayles192.PSPACE

/-- Number of vertices in the concrete matrix encoding of `Gphi`. -/
def vertexCount (n m : ℕ) : ℕ := 2 + 2*m + 2*Rc n m + n + 2*Kc n

/-- Row/column number in the order s,t,A,B,V,T,F,Y,Z. -/
def vtxNat {n m : ℕ} : Vtx n m → ℕ
  | .s => 0
  | .t => 1
  | .a j => 2 + j.val
  | .b j => 2 + m + j.val
  | .v i => 2 + 2*m + i.val
  | .ti i => 2 + 2*m + Rc n m + i.val
  | .f i => 2 + 2*m + 2*Rc n m + i.val
  | .y i => 2 + 2*m + 2*Rc n m + n + i.val
  | .z i => 2 + 2*m + 2*Rc n m + n + Kc n + i.val

lemma vtxNat_lt {n m : ℕ} (u : Vtx n m) : vtxNat u < vertexCount n m := by
  cases u <;> simp [vtxNat, vertexCount] <;> omega

/-- The concrete finite indexing. -/
def vtxFin {n m : ℕ} (u : Vtx n m) : Fin (vertexCount n m) := ⟨vtxNat u, vtxNat_lt u⟩

lemma vtxNat_injective {n m : ℕ} : Function.Injective (@vtxNat n m) := by
  intro u w h
  cases u <;> cases w <;> simp_all [vtxNat] <;> omega

lemma vtxFin_injective {n m : ℕ} : Function.Injective (@vtxFin n m) := by
  intro u w h
  apply vtxNat_injective
  exact congrArg Fin.val h

lemma card_vtx (n m : ℕ) : Fintype.card (Vtx n m) = vertexCount n m := by
  rw [← Fintype.card_congr (Vtx.proxyTypeEquiv n m)]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  simp only [vertexCount, Rc, Kc]
  omega

/-- The vertex indices of the adjacency matrix. -/
noncomputable def vtxEquiv (n m : ℕ) : Vtx n m ≃ Fin (vertexCount n m) :=
  Equiv.ofBijective vtxFin ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨vtxFin_injective, by simpa using card_vtx n m⟩)

/-- The reduction graph as a symmetric irreflexive Boolean matrix. -/
noncomputable def graphInstance (φ : PosCNF) : GraphInstance where
  n := vertexCount φ.n φ.m
  adj i j := @decide ((Gphi φ).Adj ((vtxEquiv φ.n φ.m).symm i)
    ((vtxEquiv φ.n φ.m).symm j)) (Classical.propDecidable _)
  symm := by
    intro i j
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> exact (Gphi φ).symm.symm _ _ h
  irrefl := by
    intro i
    exact @decide_eq_false _ (Classical.propDecidable _) ((Gphi φ).loopless.irrefl _)

lemma graphInstance_adj (φ : PosCNF) (u w : Vtx φ.n φ.m) :
    (graphInstance φ).graph.Adj (vtxEquiv φ.n φ.m u) (vtxEquiv φ.n φ.m w) ↔
      (Gphi φ).Adj u w := by
  simp [GraphInstance.graph, graphInstance]

/-- Duplicate clause zero exactly when the positive number of clauses is even. -/
noncomputable def oddPad (φ : PosCNF) : PosCNF where
  n := φ.n
  m := if Even φ.m ∧ 0 < φ.m then φ.m + 1 else φ.m
  clause j := if h : j.val < φ.m then φ.clause ⟨j.val, h⟩ else
    if hm : 0 < φ.m then φ.clause ⟨0, hm⟩ else ∅

lemma oddPad_n (φ : PosCNF) : (oddPad φ).n = φ.n := rfl

lemma oddPad_m (φ : PosCNF) :
    (oddPad φ).m = if Even φ.m ∧ 0 < φ.m then φ.m + 1 else φ.m := rfl

lemma oddPad_odd (φ : PosCNF) (hm : 0 < φ.m) : Odd (oddPad φ).m := by
  rw [oddPad_m]
  split_ifs with h
  · obtain ⟨r, hr⟩ := h.1
    exact ⟨r, by omega⟩
  · exact Nat.not_even_iff_odd.mp (fun he => h ⟨he, hm⟩)

lemma oddPad_clause_of_lt (φ : PosCNF) (j : Fin (oddPad φ).m) (hj : j.val < φ.m) :
    (oddPad φ).clause j = φ.clause ⟨j.val, hj⟩ := by
  simp [oddPad, hj]

lemma oddPad_clause_last (φ : PosCNF) (hm : 0 < φ.m) (j : Fin (oddPad φ).m)
    (hj : ¬ j.val < φ.m) :
    (oddPad φ).clause j = φ.clause ⟨0, hm⟩ := by
  simp [oddPad, hj, hm]

/-- A single edge, used for the empty conjunction, whose Pos CNF outcome is a True win. -/
def oneEdgeInstance : GraphInstance where
  n := 2
  adj i j := decide (i ≠ j)
  symm := by
    intro i j
    exact decide_eq_decide.mpr ne_comm
  irrefl := by
    intro i
    exact decide_eq_false (not_not_intro rfl)

/-- The complete instance map, including the empty-conjunction corner case. -/
noncomputable def reductionInstance (φ : PosCNF) : GraphInstance :=
  if φ.m = 0 then oneEdgeInstance else graphInstance (oddPad φ)

end ArcKayles192.PSPACE


