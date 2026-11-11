-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Combinatorics
-- name    : AbelianPromises_Dichotomy_Combinatorics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:24.913424+00:00
-- url     : https://prove2.me/theorems/d76eb8d7-b206-4e7e-a50d-c6ef977b0b99
-- title:
--   Valid partitions, directed cycles, tau and arithmetic progressions
-- statement:
--   A valid three-colouring of all of ℤ_p has no monochromatic zero-sum triple except (0,0,0). Two colourings are equivalent when one is obtained from the other by multiplying its input by a nonzero scalar and permuting its three colours. No additive translation is permitted. The canonical colouring is
--   $$
--   x\longmapsto 1+\lfloor3x/p\rfloor\qquad(0\le x<p).
--   $$
--   The two named colourings for p=5 have parts ({2,3},{4},{0,1}) and ({2,3},{1,4},{0}).
--
--   For a digraph E, its associated ternary relation contains (x,x,y), (x,y,x), and (y,x,x) for every arc (x,y). Bipartiteness means the endpoints of every arc have distinct Boolean colours; balance means a consistent integer height increases by one along every arc, equivalently every oriented cycle has net length zero. D₄ is the directed cycle x ↦ -2x on nonzero elements of ℤ₅.
--
--   For a normalized g with g(0)=3, τ_g is constructed by selecting the unique colour in {g(u),g(-u)}∩{1,2}. Its total definition returns colour 1 when it occurs in that pair and colour 2 otherwise; Lemma 4.8 establishes that this agrees with the unique selection, without an input certificate. An arithmetic progression has terms a+id for 0≤i<k. These objects supply the additive-combinatorial and modulus-five targets.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, Abelian embeddings make useful promises: approximation of detrivialised equations, STOC 2027 submission #967 (October 2026), printed p. 4 (PDF p. 5), Theorems 1.7–1.8; Definitions 4.5 and 4.9; Theorem D.2

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Algebra

set_option autoImplicit false

namespace AbelianPromises.Dichotomy

open PCSPBLPAff.Symmetric

/-- A valid colouring permits only the all-zero monochromatic zero-sum triple. -/
def Valid {p : ℕ} (f : ZMod p → Fin 3) : Prop :=
  ∀ x y z, x + y + z = 0 → f x = f y → f y = f z → x = 0 ∧ y = 0 ∧ z = 0

/-- No translation is allowed in the equivalence. -/
def PartitionEquivalent {p : ℕ} (f g : ZMod p → Fin 3) : Prop :=
  ∃ a : ZMod p, IsUnit a ∧ ∃ σ : Equiv.Perm (Fin 3), ∀ x, f x = σ (g (a * x))

def canonicalPartition (p : ℕ) (x : ZMod p) : Fin 3 :=
  ⟨(3 * x.val / p) % 3, Nat.mod_lt _ (by decide)⟩

def partitionFiveA (x : ZMod 5) : Fin 3 :=
  if x = 2 ∨ x = 3 then 0 else if x = 4 then 1 else 2

def partitionFiveB (x : ZMod 5) : Fin 3 :=
  if x = 2 ∨ x = 3 then 0 else if x = 1 ∨ x = 4 then 1 else 2

/-- The source's digraph-to-ternary construction, including all three placements. -/
def hat {A : Type} (E : A → A → Prop) : Relation A where
  rel _ := {t | ∃ x y, E x y ∧ (t = ![x,x,y] ∨ t = ![x,y,x] ∨ t = ![y,x,x])}

def Bipartite {A : Type} (E : A → A → Prop) : Prop :=
  ∃ b : A → Bool, ∀ x y, E x y → b x ≠ b y

/-- Equivalent height characterization of zero net length on every oriented cycle. -/
def Balanced {A : Type} (E : A → A → Prop) : Prop :=
  ∃ h : A → ℤ, ∀ x y, E x y → h y = h x + 1

abbrev FiveStar := {x : ZMod 5 // x ≠ 0}

def dFour : Relation FiveStar := hat (fun x y => y.val = -2 * x.val)

/-- The unique colour in {1,2} is represented by 0 or 1. Lemma 4.8 proves uniqueness;
this definition asks for no such proof as an input. -/
def tau {n : ℕ} (g : (Fin n → ZMod 5) → Fin 3) (u : Fin n → FiveStar) : Fin 2 :=
  if g (fun i => (u i).val) = 0 ∨ g (fun i => -(u i).val) = 0 then 0 else 1

/-- Arithmetic progression of the specified length, including the full range of indices. -/
def Progression {p : ℕ} (a d : ZMod p) (k : ℕ) : Finset (ZMod p) :=
  (Finset.range k).image fun i : ℕ => a + (i : ZMod p) * d

end AbelianPromises.Dichotomy


