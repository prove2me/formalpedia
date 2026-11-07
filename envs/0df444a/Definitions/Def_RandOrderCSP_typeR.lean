-- Prove2me | Definitions.Def_RandOrderCSP_typeR
-- name    : RandOrderCSP_typeR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:59.333106+00:00
-- url     : https://prove2.me/theorems/ce0eaec7-c314-41ed-97ab-2e108b2d4ae5
-- title:
--   Rooted hypergraph types $\mathrm{type}_R$ and the set $\mathcal N_{D,R,\Gamma}$
-- statement:
--   An **isomorphism** of colored hypergraphs is a pair of bijections on edges and vertices preserving endpoint positions and colors; for edge-rooted hypergraphs it also preserves the root. Two edges are at distance at most $R$ if a chain of at most $R$ steps through edges sharing a vertex joins them.
--
--   $\mathrm{Ball}_R(H,j)$ is the rooted hypergraph on the edges within distance $R$ of $j$ and their endpoints, and $\mathrm{type}_R(H,\chi,j)$ is its isomorphism class. $\mathcal N_{D,R,\Gamma}$ is the set of classes of connected rooted $\Gamma$-colored hypergraphs of radius $R$ and degree at most $D$.
--
--   **Formalization Note** Types are classes in a quotient of bundled finite hypergraphs, so any function of a type is invariant under relabelling, the point of footnote 4 on p.15.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.2, p.13; §3.4, pp.14–15

import Mathlib
import Definitions.Def_RandOrderCSP_compPartition

namespace RandOrderCSP

/-- A finite edge-colored `k`-uniform hypergraph, bundled with its vertex and edge sets (§3.2, p.13). -/
structure ColoredHG (k : ℕ) (C : Type) where
  /-- The vertex set. -/
  V : Type
  /-- The edge-index set. -/
  E : Type
  [fV : Fintype V]
  [fE : Fintype E]
  /-- The hypergraph. -/
  H : Hypergraph k V E
  /-- The edge coloring. -/
  col : E → C

/-- An isomorphism of colored hypergraphs (p.13): bijections `π` on edges and `ϕ` on vertices with
`ϕ(M_H(j,ℓ)) = M_{H′}(π(j),ℓ)` and `χ = χ′ ∘ π`. Endpoint positions are preserved. -/
def ColoredHG.Iso {k : ℕ} {C : Type} (A B : ColoredHG k C) (π : A.E ≃ B.E) (ϕ : A.V ≃ B.V) : Prop :=
  (∀ j ℓ, ϕ (A.H.M j ℓ) = B.H.M (π j) ℓ) ∧ ∀ j, A.col j = B.col (π j)

/-- Isomorphism of colored hypergraphs as an equivalence relation. -/
def ColoredHG.setoid (k : ℕ) (C : Type) : Setoid (ColoredHG k C) where
  r A B := ∃ π ϕ, ColoredHG.Iso A B π ϕ
  iseqv :=
    { refl := fun A => ⟨Equiv.refl _, Equiv.refl _, fun _ _ => rfl, fun _ => rfl⟩
      symm := by
        rintro A B ⟨π, ϕ, h₁, h₂⟩
        refine ⟨π.symm, ϕ.symm, fun j ℓ => ?_, fun j => ?_⟩
        · rw [Equiv.symm_apply_eq, h₁, Equiv.apply_symm_apply]
        · rw [h₂, Equiv.apply_symm_apply]
      trans := by
        rintro A B C' ⟨π, ϕ, h₁, h₂⟩ ⟨π', ϕ', h₁', h₂'⟩
        refine ⟨π.trans π', ϕ.trans ϕ', fun j ℓ => ?_, fun j => ?_⟩
        · simp [h₁, h₁']
        · simp [h₂, h₂'] }

/-- Isomorphism classes of finite colored hypergraphs. -/
def ColorClass (k : ℕ) (C : Type) : Type 1 := Quotient (ColoredHG.setoid k C)

/-- An edge-rooted colored hypergraph `(H, χ, j)` (§3.4, p.14). -/
structure RootedHG (k : ℕ) (C : Type) extends ColoredHG k C where
  /-- The designated root edge. -/
  root : E

/-- Isomorphism of rooted colored hypergraphs (p.14): additionally `π(j) = j′`. -/
def RootedHG.setoid (k : ℕ) (C : Type) : Setoid (RootedHG k C) where
  r A B := ∃ π ϕ, ColoredHG.Iso A.toColoredHG B.toColoredHG π ϕ ∧ π A.root = B.root
  iseqv :=
    { refl := fun A => ⟨Equiv.refl _, Equiv.refl _, ⟨fun _ _ => rfl, fun _ => rfl⟩, rfl⟩
      symm := by
        rintro A B ⟨π, ϕ, ⟨h₁, h₂⟩, h₃⟩
        refine ⟨π.symm, ϕ.symm, ⟨fun j ℓ => ?_, fun j => ?_⟩, ?_⟩
        · rw [Equiv.symm_apply_eq, h₁, Equiv.apply_symm_apply]
        · rw [h₂, Equiv.apply_symm_apply]
        · rw [Equiv.symm_apply_eq, h₃]
      trans := by
        rintro A B C' ⟨π, ϕ, ⟨h₁, h₂⟩, h₃⟩ ⟨π', ϕ', ⟨h₁', h₂'⟩, h₃'⟩
        refine ⟨π.trans π', ϕ.trans ϕ', ⟨fun j ℓ => ?_, fun j => ?_⟩, ?_⟩
        · simp [h₁, h₁']
        · simp [h₂, h₂']
        · simp [h₃, h₃'] }

/-- Isomorphism classes of finite rooted colored hypergraphs. -/
def RootedClass (k : ℕ) (C : Type) : Type 1 := Quotient (RootedHG.setoid k C)

variable {k : ℕ} {V E C : Type}

/-- `dist_H(j, j′) ≤ R` (p.14): there are edges `j = j₀, …, j_r = j′`, `r ≤ R`, with `j_{i-1}` and `j_i`
sharing a vertex. -/
def edgeDistLE (H : Hypergraph k V E) (j j' : E) (R : ℕ) : Prop :=
  ∃ r ≤ R, ∃ w : Fin (r + 1) → E, w 0 = j ∧ w (Fin.last r) = j' ∧
    ∀ i : Fin r, ∃ ℓ ℓ', H.M (w i.castSucc) ℓ = H.M (w i.succ) ℓ'

/-- `N_{D,R,Γ}` (§3.4, p.14) as a set of rooted isomorphism classes: "the set of connected, rooted,
Γ-colored, radius-R, degree-at-most-D hypergraphs up to isomorphism." -/
def nbhdTypes (k D R : ℕ) (C : Type) : Set (RootedClass k C) :=
  {x | ∃ A : RootedHG k C, Quotient.mk (RootedHG.setoid k C) A = x ∧
    A.H.incidenceGraph.Connected ∧
    (∀ j, edgeDistLE A.H A.root j R) ∧
    ∀ v, Nat.card {j // ∃ ℓ, A.H.M j ℓ = v} ≤ D}

/-- `Ball_R(H, j)` (p.15) with its coloring: "the rooted hypergraph Ball_R(H, j) with root j whose edges
are the edges j′ ∈ ℰ_H with dist_H(j, j′) ≤ R, and whose vertices are their endpoints." -/
noncomputable def ball [Finite V] [Finite E] (H : Hypergraph k V E) (χ : E → C) (j : E) (R : ℕ) :
    RootedHG k C where
  V := {v // ∃ j' ℓ, edgeDistLE H j j' R ∧ H.M j' ℓ = v}
  E := {j' // edgeDistLE H j j' R}
  fV := Fintype.ofFinite _
  fE := Fintype.ofFinite _
  H :=
    { M := fun j' ℓ => ⟨H.M j'.1 ℓ, j'.1, ℓ, j'.2, rfl⟩
      row_inj := fun j' _ _ h => H.row_inj j'.1 (congrArg Subtype.val h) }
  col := fun j' => χ j'.1
  root := ⟨j, 0, Nat.zero_le _, fun _ => j, rfl, rfl, fun i => i.elim0⟩

/-- **`type_R(H, χ, j)`** (§3.4, p.15).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.15: "We let type_R(H, χ, j) ∈ N_{D,R,Γ} denote the
isomorphism class of the colored, rooted hypergraph Ball_R(H, j)."

**Formalization Note.** Types are isomorphism classes of bundled finite hypergraphs (a `Quotient`), so
a function of a type is invariant under relabelling (footnote 4, p.15). `RootedClass k C` holds all
finite classes; `nbhdTypes k D R C` is the subset `N_{D,R,C}`, which the paper notes is finite. This
module also holds `ColoredHG`, `RootedHG`, their isomorphisms, `edgeDistLE`, `nbhdTypes` and `ball`. -/
noncomputable def typeR [Finite V] [Finite E] (H : Hypergraph k V E) (χ : E → C) (j : E) (R : ℕ) :
    RootedClass k C :=
  Quotient.mk (RootedHG.setoid k C) (ball H χ j R)

end RandOrderCSP


