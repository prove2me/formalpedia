-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
-- name    : OAI_Combinatorics_Hamiltonian_Forest
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:37:22.438483+00:00
-- url     : https://prove2.me/theorems/f33fa070-307b-4820-989e-e175ac43897d
-- title:
--   Orbit coordinates for successor permutations and dual cycles of paired states
-- statement:
--   This file enumerates orbits of permutations cyclically and uses this to turn orbits of the successor permutation of a pair of states into cycles of a dual graph.
--
--   **Triangle systems and pairs.** A triangle system $T$ has a set $A$ of triangles and a set of points; each triangle $t$ has three distinct corners $T(t,0),T(t,1),T(t,2)$ (indices in $\mathbb{Z}/3$), and two distinct triangles never share two corners. For a set $X$ of points, a *state* is a map $s:A\to\mathbb{Z}/3$ such that $t\mapsto T(t,s(t))$ is a bijection from $A$ onto $X$; two states $r,s$ are *partners* if $r(t)\ne s(t)$ for all $t$, and a *pair* $P=(\ell,\rho)$ is an ordered pair of partner states. Its *successor permutation* $\sigma_P$ of $A$ is defined by $T(\sigma_P(t),\ell(\sigma_P(t)))=T(t,\rho(t))$; it has no fixed points.
--
--   **Colored dual setting.** $N$ and $D$ are networks on finite vertex sets $V$ and $F$ with a common finite edge set $E$: every edge has a tail and a head in $V$ (for $N$) and in $F$ (for $D$), and the graph of a network joins two distinct vertices when some edge runs between them. A colored dual structure on $(N,D)$ records that $N$ and $D$ are connected, simple and mutually dual (the cycle space of each equals the cut space of the other), that $N$ is cubic with a black/white colouring in which every edge has exactly one black endpoint, and it assigns to each $v\in V$ a triangle $\Delta_v$ of $D$ with distinct corners $c_v(0),c_v(1),c_v(2)\in F$ (indices in $\mathbb{Z}/3$) whose three sides are exactly the edges of $N$ at $v$, the side with index $k$ joining $c_v(k)$ and $c_v(k+1)$, with compatible orientations in $N$ and $D$. For a root $v_0\in V$ let $B$ be the set of black vertices other than $v_0$, and $F^\circ=F\setminus\{c_{v_0}(0),c_{v_0}(1),c_{v_0}(2)\}$. A *state* is a map $s:B\to\mathbb{Z}/3$ such that $t\mapsto c_t(s(t))$ is a bijection from $B$ onto $F^\circ$. The triangles $\Delta_t$, $t\in B$, form a triangle system with point set $F$, and its states for $X=F^\circ$ are exactly these states. A *state cycle* of a state $s$ is a cyclic sequence $y_0,\dots,y_{m+2}$ of distinct vertices of the graph of $D$ (indices modulo $m+3$, consecutive vertices adjacent) together with triangles $t_k\in B$ and corner indices $j_k$ such that $c_{t_k}(s(t_k))=y_k$ and $c_{t_k}(j_k)=y_{k+1}$ for all $k$. The *opposite graph* of $s$ joins two distinct points of $F$ when they are corners of a common triangle $\Delta_t$, $t\in B$, both different from $c_t(s(t))$. An *opposite cycle* of $s$ is a cyclic sequence $y_0,\dots,y_{m+2}$ of distinct points, consecutive ones adjacent in the opposite graph, together with distinct triangles $t_k\in B$ and corner indices $\lambda_k,\mu_k$ different from $s(t_k)$ with $c_{t_k}(\lambda_k)=y_k$ and $c_{t_k}(\mu_k)=y_{k+1}$.
--
--   1. **Permutation coordinates.** For a permutation $p$ of a set $A$ and $a\in A$, permutation coordinates consist of $n\in\mathbb{N}$ and an injective map $f:\mathbb{Z}/(n+3)\to A$ such that
--   $$
--   f(k+1)=p\bigl(f(k)\bigr)\ \text{ for all }k\in\mathbb{Z}/(n+3),\qquad f\bigl(\mathbb{Z}/(n+3)\bigr)=\{p^m(a): m\in\mathbb{Z}\}.
--   $$
--   If $A$ is finite, $p(a)\ne a$ and $p(p(a))\ne a$, such coordinates exist: the orbit of $a$ is a cycle of length $n+3\ge 3$.
--   2. **No two-cycles.** For every pair $P$ and every triangle $t$, $\sigma_P(\sigma_P(t))\ne t$. Hence for finite $A$ every orbit of $\sigma_P$ has at least three elements, and the file fixes permutation coordinates of $\sigma_P$ at each $a\in A$.
--   3. **The paired cycle of an orbit.** Let $P=(\ell,\rho)$ be a pair of states in the colored dual setting, $a\in B$, and $f$ the fixed coordinates of $\sigma_P$ at $a$. Then the points $y_k=c_{f(k)}(\ell(f(k)))$, with triangles $f(k)$ and corner indices $\rho(f(k))$, form a state cycle of the left state $\ell$; here $y_{k+1}=c_{f(k)}(\rho(f(k)))$, so consecutive points are two corners of one triangle.
--   4. **Forward state cycles from opposite cycles.** Let $(y_k,t_k,\lambda_k,\mu_k)$ be an opposite cycle of a state $s$, and $r$ a partner of $s$ with $c_{t_k}(r(t_k))=y_k$ for all $k$. With the third index $\theta_k=-(r(t_k)+s(t_k))$ one has $c_{t_k}(\theta_k)=y_{k+1}$, and $(y_k,t_k,\theta_k)$ is a state cycle of $r$ through the same points.
--   5. **Connected components.** For a network $H$ on a finite vertex set, its components are the connected components of its graph; they form a finite set, and each vertex is mapped to its component.
--
--   Items 3 and 4 convert pairs of states into cycles of the dual graph, where index sums and weight differences along cycles can be computed using the duality between $N$ and $D$; the module uses them to find a pair whose right state has an acyclic opposite graph (a forest). Item 5 provides the component map used for functions that are constant on components.
--
--   **Formalization Note** Coordinates are the structure `PermutationCoordinates`; the orbit is the `SameCycle` class of $a$, and $f(0)$ need not equal $a$. Existence is `permutationCoordinates_exists`, the choice is `cycleCoordinates`, item 2 is `next_next_ne`, items 3 and 4 are `pairedCycle` and `oppositeForward` (the identity $c_{t_k}(\theta_k)=y_{k+1}$ is `opposite_forward_end`), and item 5 consists of `Components`, the instance `componentsFintype` and `componentMap`. States and pairs in items 3 and 4 are those of the triangle system `M.system root` on the point set `M.nonroots root`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Forest.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Forest.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials

namespace OAI

/-! Common-phase nonvanishing and forest extraction from actual states. -/

namespace Barnette
noncomputable section
open scoped Classical

structure PermutationCoordinates {A : Type*} (p : Equiv.Perm A) (a : A) where
  n : ℕ
  face : Fin (n+3) ↪ A
  step : ∀ i, face (i+1) = p (face i)
  range_eq : Set.range face = {b | p.SameCycle a b}

lemma permutationCoordinates_exists {A : Type*} [Finite A] (p : Equiv.Perm A) (a : A)
    (h1 : p a ≠ a) (h2 : p (p a) ≠ a) : Nonempty (PermutationCoordinates p a) := by
  have hp : 0 < Function.minimalPeriod p a :=
    Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts a)
  have hp1 : Function.minimalPeriod p a ≠ 1 := by
    intro hh
    have hh' := Function.iterate_minimalPeriod (f := (p : A → A)) (x := a)
    rw [hh] at hh'
    exact h1 (by simpa using hh')
  have hp2 : Function.minimalPeriod p a ≠ 2 := by
    intro hh
    have hh' := Function.iterate_minimalPeriod (f := (p : A → A)) (x := a)
    rw [hh] at hh'
    exact h2 (by simpa [Function.iterate_succ_apply] using hh')
  let n := Function.minimalPeriod p a - 3
  have hn : n+3 = Function.minimalPeriod p a := by omega
  let f : Fin (n+3) → A := fun i => (p : A → A)^[i.val] a
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod (by simpa only [← hn, Set.mem_Iio] using i.isLt)
      (by simpa only [← hn, Set.mem_Iio] using j.isLt) hij
  refine ⟨⟨n,⟨f,hf⟩,?_,?_⟩⟩
  · intro i
    change (p : A → A)^[(i+1).val] a = p ((p : A → A)^[i.val] a)
    have hval : (i+1).val = (i.val+1) % Function.minimalPeriod p a := by
      rw [Fin.val_add]
      simp only [Fin.val_one,hn]
    rw [hval,Function.iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']
  · ext b
    constructor
    · rintro ⟨i,rfl⟩
      change p.SameCycle a ((p : A → A)^[i.val] a)
      rw [← Equiv.Perm.coe_pow]
      exact (Equiv.Perm.SameCycle.refl p a).pow_right
    · intro hb
      obtain ⟨m,hm⟩ := hb.exists_nat_pow_eq
      refine ⟨⟨m % Function.minimalPeriod p a,by rw [hn]; exact Nat.mod_lt _ hp⟩,?_⟩
      change (p : A → A)^[m % Function.minimalPeriod p a] a = b
      rw [Function.iterate_mod_minimalPeriod_eq,← Equiv.Perm.coe_pow,hm]

namespace TriangleSystem.Pair
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

lemma next_next_ne (P : @Pair A V T X) (t : A) : P.next (P.next t) ≠ t := by
  intro hh
  have hrt : P.left.val t ≠ P.right.val t := fun he =>
    P.partner t ((State.value_eq_iff _ _ _).mpr he)
  have hru : P.right.val (P.next t) ≠ P.left.val (P.next t) := fun he =>
    P.partner (P.next t) ((State.value_eq_iff _ _ _).mpr he.symm)
  have hx : T.vertex t (P.left.val t) = T.vertex (P.next t) (P.right.val (P.next t)) := by
    change P.left.value t = P.right.value (P.next t)
    rw [← P.value_next,hh]
  have hy : T.vertex t (P.right.val t) = T.vertex (P.next t) (P.left.val (P.next t)) :=
    (P.value_next t).symm
  exact P.next_ne t (T.edge_unique _ _ _ _ _ _ hrt hru hx hy).symm

variable [Fintype A]

def cycleCoordinates (P : @Pair A V T X) (a : A) : PermutationCoordinates P.next a :=
  (permutationCoordinates_exists P.next a (P.next_ne a) (P.next_next_ne a)).some

end TriangleSystem.Pair
end
end Barnette
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

def pairedCycle (P : (M.system root).Pair (M.nonroots root)) (a : M.Black root) :
    M.StateCycle P.left where
  cycle :=
    { n := (P.cycleCoordinates a).n
      vertex := ⟨fun i => P.left.value ((P.cycleCoordinates a).face i),
        P.left.value_injective.comp (P.cycleCoordinates a).face.injective⟩
      adjacent := by
        intro i
        let t := (P.cycleCoordinates a).face i
        have ht : P.left.value ((P.cycleCoordinates a).face (i+1)) = P.right.value t := by
          rw [(P.cycleCoordinates a).step,P.value_next]
        change D.graph.Adj (P.left.value t) (P.left.value ((P.cycleCoordinates a).face (i+1)))
        rw [ht]
        have hij : P.left.val t ≠ P.right.val t := fun hh =>
          P.partner t ((State.value_eq_iff _ _ _).mpr hh)
        exact ⟨P.partner t,(M.face t.val).side D (P.left.val t) (P.right.val t),
          Sym2.eq_iff.mp ((M.face t.val).side_ends D hij)⟩ }
  face := (P.cycleCoordinates a).face
  corner i := P.right.val ((P.cycleCoordinates a).face i)
  left_eq _ := rfl
  right_eq i := by
    change P.right.value ((P.cycleCoordinates a).face i) =
      P.left.value ((P.cycleCoordinates a).face (i+1))
    rw [(P.cycleCoordinates a).step,P.value_next]

omit [Fintype F] in
lemma opposite_forward_end {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) (i : Fin (C.cycle.n+3)) :
    (M.system root).vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
      C.cycle.vertex (i+1) := by
  rcases C.partner_endpoints hrs i with ⟨_,he⟩ | ⟨he,_⟩
  · exact he
  · exact ((C.cycle.adjacent i).1 ((hf i).symm.trans he)).elim

def oppositeForward {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) : M.StateCycle r where
  cycle :=
    { n := C.cycle.n
      vertex := C.cycle.vertex
      adjacent i := by
        have hij : r.val (C.face i) ≠ thirdIndex (r.val (C.face i)) (s.val (C.face i)) :=
          (thirdIndex_distinct _ _ (fun hh => hrs _ ((State.value_eq_iff _ _ _).mpr hh))).1.symm
        have he := (M.face (C.face i).val).side_ends D hij
        change s(D.tail _,D.head _) = s(r.value (C.face i),
          (M.system root).vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i)))) at he
        rw [hf,M.opposite_forward_end C hrs hf] at he
        exact ⟨(C.cycle.adjacent i).1,_,Sym2.eq_iff.mp he⟩ }
  face := C.face
  corner i := thirdIndex (r.val (C.face i)) (s.val (C.face i))
  left_eq := hf
  right_eq := M.opposite_forward_end C hrs hf

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {F : Type*} [Fintype F]
abbrev Components (H : Network F E) := H.graph.ConnectedComponent

instance componentsFintype (H : Network F E) : Fintype H.Components := Fintype.ofFinite _

def componentMap (H : Network F E) : F → H.Components := H.graph.connectedComponentMk

end
end Barnette.Network

end OAI


