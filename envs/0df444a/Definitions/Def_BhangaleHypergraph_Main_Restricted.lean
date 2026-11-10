-- Prove2me | Definitions.Def_BhangaleHypergraph_Main_Restricted
-- name    : BhangaleHypergraph_Main_Restricted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:05:24.836195+00:00
-- url     : https://prove2.me/theorems/87a596f1-75f3-4e33-8c20-e18fa68b25b0
-- title:
--   Schrijver graphs, restricted NAE colorings, minors and local cores
-- statement:
--   Let $[R]$ be a finite ordered label set, $C$ a number of colors and $s$ a size parameter. A test domain is a family $W\subseteq2^{[R]}$ containing $\varnothing$ and $[R]$. A coloring is admissible when it preserves not-all-equal on every retained triple whose union is $[R]$ and whose threefold intersection is empty, including repeated inputs. A set $S$ avoids $T$ when every retained superset of $S$ receives a color outside $T$.
--
--   The exact minor identity for a total map $\pi:[R]\to[R']$ requires both inverse-image closure and $g(B)=f(\pi^{-1}B)$ on the entire target domain. Surjectivity is not assumed.
--
--   The Schrijver graph has stable $h$-subsets of the inherited cycle as vertices and disjointness as adjacency. The local core $U_{C,s}$ includes the small sets, their complements, and every prescribed Schrijver copy (or the full residual cube when the residual size is at most $C$) from Definition 2.15. The size parameter for selector inputs is $s=C^{C-1}$.
--
--   These definitions provide the shared local objects for the combinatorial milestones. Label and color indices use zero-based finite types. A selector and its consistency are not fields of an admissible coloring.
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), §§2.3–2.6 and §3.3, pp. 8–16 (printed pages = PDF pages); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Mathlib

namespace BhangaleHypergraph.Main

/-- Cyclic successor in the inherited increasing order, not the ambient cycle. -/
def CyclicNext {R : ℕ} (Z : Finset (Fin R)) (a b : Fin R) : Prop :=
  ∃ i < Z.card, (Z.sort (· ≤ ·))[i]? = some a ∧
    (Z.sort (· ≤ ·))[(i + 1) % Z.card]? = some b

def StableOn {R : ℕ} (Z H : Finset (Fin R)) : Prop :=
  H ⊆ Z ∧ ∀ a ∈ H, ∀ b ∈ H, a ≠ b → ¬ CyclicNext Z a b

def SchrijverVertex (m h : ℕ) :=
  {H : Finset (Fin m) // H.card = h ∧ StableOn Finset.univ H}

noncomputable instance (m h : ℕ) : Fintype (SchrijverVertex m h) := by
  classical
  unfold SchrijverVertex
  exact Fintype.ofFinite _

def Schrijver (m h : ℕ) : SimpleGraph (SchrijverVertex m h) where
  Adj A B := A ≠ B ∧ Disjoint A.val B.val
  symm := ⟨by intro A B h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro A h; exact h.1 rfl⟩

/-- The categorical graph product with the complete graph on `C+1` vertices. -/
def ProductComplete {V : Type} (G : SimpleGraph V) (C : ℕ) :
    SimpleGraph (V × Fin (C + 1)) where
  Adj a b := G.Adj a.1 b.1 ∧ a.2 ≠ b.2
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro a h; exact h.2 rfl⟩

/-- Boolean coordinatewise NAE, with repeated inputs permitted. -/
def BooleanNAE {R : ℕ} (A B D : Finset (Fin R)) : Prop :=
  A ∪ B ∪ D = Finset.univ ∧ A ∩ B ∩ D = ∅

def TestDomain {R : ℕ} (W : Finset (Finset (Fin R))) : Prop :=
  ∅ ∈ W ∧ Finset.univ ∈ W

def Admissible {R C : ℕ} {W : Finset (Finset (Fin R))} (f : W → Fin C) : Prop :=
  ∀ A B D : W, BooleanNAE A.val B.val D.val → ¬ (f A = f B ∧ f B = f D)

/-- The subset itself need not be retained in the test domain. -/
def Avoids {R C : ℕ} {W : Finset (Finset (Fin R))} (f : W → Fin C)
    (S : Finset (Fin R)) (T : Finset (Fin C)) : Prop :=
  ∀ X : W, S ⊆ X.val → f X ∉ T

def AvoidsNumber {R C : ℕ} {W : Finset (Finset (Fin R))} (f : W → Fin C)
    (S : Finset (Fin R)) (t : ℕ) : Prop :=
  ∃ T : Finset (Fin C), T.card = t ∧ Avoids f S T

def Preimage {R R' : ℕ} (π : Fin R → Fin R') (B : Finset (Fin R')) : Finset (Fin R) :=
  Finset.univ.filter fun a => π a ∈ B

/-- Closure is part of an exact minor identity, but surjectivity is not. -/
def ExactMinor {R R' C : ℕ} {W : Finset (Finset (Fin R))}
    {W' : Finset (Finset (Fin R'))} (f : W → Fin C) (g : W' → Fin C)
    (π : Fin R → Fin R') : Prop :=
  ∀ B : W', ∃ h : Preimage π B.val ∈ W, g B = f ⟨Preimage π B.val, h⟩

/-- Definition 2.15, including the complete small-residual-cube branch. -/
noncomputable def Core (C s R : ℕ) : Finset (Finset (Fin R)) := by
  classical
  exact Finset.univ.filter fun X =>
    X.card ≤ (C + 1) * s + C ∨ (Finset.univ \ X).card ≤ (C + 1) * s + C ∨
    ∃ P : Finset (Fin R), P.card ≤ (C + 1) * s ∧
      ∃ A : Finset (Fin R), A ⊆ P ∧ ∃ H : Finset (Fin R),
        X = A ∪ H ∧
        (if C < (Finset.univ \ P).card then
          H.card = ((Finset.univ \ P).card - C + 1) / 2 ∧ StableOn (Finset.univ \ P) H
        else H ⊆ Finset.univ \ P)

/-- All admissible, positive-arity colorings on core-containing domains.
No selector, type, or consistency property is assumed. -/
structure CoreColoring (C : ℕ) where
  R : ℕ
  positive : 0 < R
  W : Finset (Finset (Fin R))
  core_subset : Core C (C ^ (C - 1)) R ⊆ W
  color : W → Fin C
  admissible : Admissible color

end BhangaleHypergraph.Main


