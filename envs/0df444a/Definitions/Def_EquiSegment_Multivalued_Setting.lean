-- Prove2me | Definitions.Def_EquiSegment_Multivalued_Setting
-- name    : EquiSegment_Multivalued_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:38.462622+00:00
-- url     : https://prove2.me/theorems/bba984db-a93b-44a6-b261-86571dfaac6a
-- title:
--   Definition 2.1 and §4 — segment cylinder, nice graphs, and zero partitions
-- statement:
--   Let $\mathcal I$ consist of endpoint pairs $(a,b)$ with $0\le a\le b\le1$, representing possibly degenerate segments $[a,b]$. The cylinder is $C=\mathcal I\times[-1,1]$, with bottom $B=\mathcal I\times\{-1\}$ and top $T=\mathcal I\times\{1\}$. A set $Z$ separates $B$ from $T$ when both sides avoid $Z$ and lie in different connected components of $C\setminus Z$. A **nice multivalued function** is a compact graph $Z\subseteq\mathcal I\times(-1,1)$ with this separation property.
--
--   A **representation** $\varphi$ is continuous on $C$, negative on $B$, and positive on $T$. Its zero set is $\{(I,y)\in C:\varphi(I,y)=0\}$. The degenerate identity condition is $\varphi([a,a],y)=y$ for $a\in[0,1]$ and $y\in[-1,1]$.
--
--   For $p\in\mathbb N$, a zero partition of $I=[a,b]$ at value $y$ consists of exactly $p$ consecutive possibly degenerate segments with endpoints $a=x_0\le\cdots\le x_p=b$, each satisfying $\varphi([x_{j-1},x_j],y)=0$. The projected set $Z_p(\varphi)$ contains exactly the cylinder points $(I,y)$ admitting such a partition.
--
--   These definitions state the objects used by Lemmas 2.2 and 2.3 and Claims 4.3–4.4. Values of the total Lean function outside the cylinder have no mathematical role.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 2–3, 7–9, Definition 2.1; equation (4.1); Claim 4.4

import Mathlib

namespace EquiSegment.Multivalued

/-- The possibly degenerate subsegments of `[0, 1]`, represented by endpoint pairs. -/
def Seg : Set (ℝ × ℝ) := {s | 0 ≤ s.1 ∧ s.1 ≤ s.2 ∧ s.2 ≤ 1}

/-- The cylinder over the space of subsegments. -/
def Cyl : Set ((ℝ × ℝ) × ℝ) := Seg ×ˢ Set.Icc (-1) 1

def Bottom : Set ((ℝ × ℝ) × ℝ) := Seg ×ˢ {(-1 : ℝ)}
def Top : Set ((ℝ × ℝ) × ℝ) := Seg ×ˢ {(1 : ℝ)}

/-- The two designated sides avoid `Z` and lie in different components of its complement. -/
def Separates {α : Type*} [TopologicalSpace α] (X Z A B : Set α) : Prop :=
  A ⊆ X \ Z ∧ B ⊆ X \ Z ∧
    ∀ a ∈ A, ∀ b ∈ B, b ∉ connectedComponentIn (X \ Z) a

/-- Definition 2.1: a nice multivalued function, identified with its graph. -/
def IsNice (Z : Set ((ℝ × ℝ) × ℝ)) : Prop :=
  IsCompact Z ∧ Z ⊆ Seg ×ˢ Set.Ioo (-1) 1 ∧ Separates Cyl Z Bottom Top

/-- A continuous representation with negative and positive cylinder boundary values. -/
def IsRep (φ : ℝ × ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun x : (ℝ × ℝ) × ℝ => φ x.1 x.2) Cyl ∧
    ∀ s ∈ Seg, φ s (-1) < 0 ∧ 0 < φ s 1

def zeroSet (φ : ℝ × ℝ → ℝ → ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {x ∈ Cyl | φ x.1 x.2 = 0}

/-- The representation restricts to the identity on degenerate segments. -/
def DegId (φ : ℝ × ℝ → ℝ → ℝ) : Prop :=
  ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, φ (a, a) y = y

/-- A partition into exactly `p` consecutive, possibly degenerate zero segments. -/
def IsZeroPartition (φ : ℝ × ℝ → ℝ → ℝ) (p : ℕ) (s : ℝ × ℝ) (y : ℝ) : Prop :=
  ∃ x : Fin (p + 1) → ℝ, Monotone x ∧ x 0 = s.1 ∧ x (Fin.last p) = s.2 ∧
    ∀ i : Fin p, φ (x i.castSucc, x i.succ) y = 0

/-- The projection of the simultaneous-zero set from labeled partitions. -/
def projZ (φ : ℝ × ℝ → ℝ → ℝ) (p : ℕ) : Set ((ℝ × ℝ) × ℝ) :=
  {x ∈ Cyl | IsZeroPartition φ p x.1 x.2}

end EquiSegment.Multivalued


