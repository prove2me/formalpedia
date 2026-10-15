-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay
-- name    : OAI_Combinatorics_InfiniteMatroid_DoubleRay
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:07:06.559053+00:00
-- url     : https://prove2.me/theorems/19ff514d-bb94-4e1b-af83-0daf6db29f7c
-- title:
--   Double-ray sums: parity vertices, inward and outward bundles, and the ray matroid
-- statement:
--   Let $\alpha$ be a type and let $Q$ be a matroid on $\alpha\times\{0,1\}$. The ground set of the new matroids is $\mathbb Z\times\alpha$, split into *bundles* $\{k\}\times\alpha$, $k\in\mathbb Z$. Picture the bundles as the edges of a double ray whose vertices are the integers, vertex $n$ being incident with the edges $n-1$ and $n$; the *central edge* is $-1$, between the vertices $-1$ and $0$.
--
--   1. **Inward and outward bundle at a vertex.** For $n\in\mathbb Z$ and $b\in\{0,1\}$,
--   $$\beta(n,b)=\begin{cases} n, & n<0,\ b=0,\\ n-1, & n<0,\ b=1,\\ n-1, & n\ge 0,\ b=0,\\ n, & n\ge 0,\ b=1.\end{cases}$$
--   Thus $\beta(n,0)$ is the edge at $n$ on the side of the central edge (inward) and $\beta(n,1)$ is the edge pointing away from it (outward).
--   2. **Parity vertices.** For a parity bit $p\in\{0,1\}$ let $V_p=\{n\in\mathbb Z: n\bmod 2=p\}$ (even vertices for $p=0$, odd vertices for $p=1$).
--   3. **Component maps.** For $v\in V_p$ the map $\kappa_v:\alpha\times\{0,1\}\to\mathbb Z\times\alpha$, $\kappa_v(x,b)=(\beta(v,b),x)$, places a copy of $\alpha\times\{0,1\}$ on the two edges at $v$. The combined map $V_p\times(\alpha\times\{0,1\})\to\mathbb Z\times\alpha$, $(v,(x,b))\mapsto\kappa_v(x,b)$, is a bijection, because every edge $k$ is incident with exactly one vertex of parity $p$ (namely $k$ or $k+1$) and $\beta(v,\cdot)$ takes the values $v-1$ and $v$ once each.
--   4. **Ray matroid.** $M_p(Q)$ is the image of the direct sum $\bigoplus_{v\in V_p}Q$ under this bijection. Concretely, $I\subseteq\mathbb Z\times\alpha$ is independent in $M_p(Q)$ exactly when $\kappa_v^{-1}(I)$ is independent in $Q$ for every $v\in V_p$.
--   5. **Vertex assignment.** For $I\subseteq\mathbb Z\times\alpha$ and $n\in\mathbb Z$,
--   $$A_n(I)=\begin{cases}\{(x,b): (\beta(n,b),x)\in I\}, & n \text{ even},\\ \{(x,b): (\beta(n,b),x)\notin I\}, & n\text{ odd},\end{cases}$$
--   the local trace at vertex $n$ of $I$ (even $n$) or of its complement (odd $n$).
--
--   In the counterexample, $\alpha=D$, $Q$ is the self-dual matroid on $E_0=D\times\{0,1\}$, and the two matroids on $\mathbb Z\times D$ are $M_0(Q)$ and $M_1(Q)$; both are self-dual because $Q$ is. If $I$ is independent in $M_0(Q)$ and its complement is independent in $M_1(Q)$, then every $A_n(I)$ is independent in $Q$, which is how a putative independent partition of $\mathbb Z\times D$ is transferred to the vertices.
--
--   **Formalization Note** The definitions are `bundleAt` ($\beta$; `false` is $0$, `true` is $1$), `parityBit`, `Vertex p` (the subtype of integers with `n % 2 = parityBit p`), `componentMap`, `globalComponentMap`, `componentEquiv` (the bijection, built with `Equiv.ofBijective`; the injectivity and surjectivity arguments are inlined), `rayMatroid Q p = (Matroid.sum' (fun _ => Q)).mapEquiv (componentEquiv α p)` and `assignment`. The characterization of independence and the self-duality are separate lemmas of the source module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/DoubleRay.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/DoubleRay.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroid mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_TransfiniteConstruction

namespace OAI

section
open Set Matroid
namespace InfiniteMatroidCounterexample

/-- Inward (false) and outward (true) bundles with the central edge at -1. -/
def bundleAt (n : ℤ) (b : Bool) : ℤ :=
  if n < 0 then (if b then n - 1 else n) else (if b then n else n - 1)

def parityBit (p : Bool) : ℤ := if p then 1 else 0
abbrev Vertex (p : Bool) := {n : ℤ // n % 2 = parityBit p}

def componentMap {α : Type*} {p : Bool} (v : Vertex p) (x : α × Bool) : ℤ × α :=
  (bundleAt v x.2,x.1)

def globalComponentMap (α : Type*) (p : Bool) (x : Vertex p × (α × Bool)) : ℤ × α :=
  componentMap x.1 x.2

noncomputable def componentEquiv (α : Type*) (p : Bool) : (Vertex p × (α × Bool)) ≃ (ℤ × α) :=
  Equiv.ofBijective (globalComponentMap α p) (by
    have bundleAt_bounds (n : ℤ) (b : Bool) : n - 1 ≤ bundleAt n b ∧ bundleAt n b ≤ n := by
      unfold bundleAt
      split_ifs <;> omega
    have bundleAt_injective (n : ℤ) : Function.Injective (bundleAt n) := by
      intro b c h
      cases b <;> cases c <;> simp_all [bundleAt] <;> split_ifs at h <;> omega
    have bundleAt_right (n : ℤ) : ∃ b, bundleAt n b = n := by
      by_cases h : n < 0
      · exact ⟨false,by simp [bundleAt,h]⟩
      · exact ⟨true,by simp [bundleAt,h]⟩
    have bundleAt_left (n : ℤ) : ∃ b, bundleAt n b = n - 1 := by
      by_cases h : n < 0
      · exact ⟨true,by simp [bundleAt,h]⟩
      · exact ⟨false,by simp [bundleAt,h]⟩

    have globalComponentMap_injective :
        Function.Injective (globalComponentMap α p) := by
      rintro ⟨⟨n,hn⟩,d,b⟩ ⟨⟨m,hm⟩,e,c⟩ h
      have hnm : bundleAt n b = bundleAt m c := congrArg Prod.fst h
      have hde : d = e := congrArg Prod.snd h
      have hb := bundleAt_bounds n b
      have hc := bundleAt_bounds m c
      have hnm' : n = m := by omega
      subst m
      have hbc := bundleAt_injective n hnm
      subst e; subst c
      rfl

    have globalComponentMap_surjective :
        Function.Surjective (globalComponentMap α p) := by
      rintro ⟨n,d⟩
      by_cases hn : n % 2 = parityBit p
      · obtain ⟨b,hb⟩ := bundleAt_right n
        exact ⟨(⟨n,hn⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
      · have hn' : (n+1) % 2 = parityBit p := by
          cases p <;> simp only [parityBit,Bool.false_eq_true,ite_false,ite_true] at hn ⊢ <;> omega
        obtain ⟨b,hb⟩ := bundleAt_left (n+1)
        exact ⟨(⟨n+1,hn'⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
    exact ⟨globalComponentMap_injective, globalComponentMap_surjective⟩)

noncomputable def rayMatroid {α : Type*} (Q : Matroid (α × Bool)) (p : Bool) : Matroid (ℤ × α) :=
  (Matroid.sum' (fun _ : Vertex p ↦ Q)).mapEquiv (componentEquiv α p)

/-- The independent partition is assigned to vertices by parity. -/
def assignment {α : Type*} (I : Set (ℤ × α)) (n : ℤ) : Set (α × Bool) :=
  {x | if n % 2 = 0 then (bundleAt n x.2,x.1) ∈ I else (bundleAt n x.2,x.1) ∉ I}

end InfiniteMatroidCounterexample
end

end OAI


