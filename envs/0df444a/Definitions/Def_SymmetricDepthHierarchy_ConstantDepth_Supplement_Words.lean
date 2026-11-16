-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Words
-- name    : SymmetricDepthHierarchy_ConstantDepth_Supplement_Words
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:57:43.466655+00:00
-- url     : https://prove2.me/theorems/a91bdfec-eb40-4b2a-988e-58118568eb35
-- title:
--   Bilabelled atomic words, gluing, quotient patterns, and homomorphism matrices
-- statement:
--   For $c\ge0$, there are $c+1$ left and $c+1$ right slots. A bilabelled pattern has side-respecting input and output maps from these slots, which need not be injective. Series composition takes a disjoint union and identifies matching output and input vertices. The closure identifies each input label with its output label. Quotients sum edge multiplicities over all preimages.
--
--   The identity is the edgeless slot graph. Atomic edge graphs add one edge between a left and right slot; reset graphs add a fresh output vertex on the specified side. A word $u$ denotes the left fold starting at the identity, including the empty word. With $L_n=[n]^\Sigma$, its homomorphism matrix has rows and columns indexed by $L_n$:
--   $$ (F_n)_{a,b}=\sum_{h\alpha=a,\ h\beta=b}\prod_{xy\in E(F)}x_{h(x),h(y)}.$$
--   All vertex assignments respect sides; edge occurrences and isolated vertices are preserved. Pattern isomorphism is given by separate side bijections preserving multiplicity. This operational interface does not assume the matrix identities or pathwidth bounds proved in Lemma C.2.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 42–43 (PDF p. 45–46), §C.2; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Paths

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement


/-- C.2 bilabelled bipartite multigraph; labels need not be injective. -/
structure BiPattern (c : ℕ) where
  pattern : Pattern
  inL : Fin (c+1) → pattern.A
  inR : Fin (c+1) → pattern.B
  outL : Fin (c+1) → pattern.A
  outR : Fin (c+1) → pattern.B

/-- Quotient preserves every edge occurrence, including parallel edges created by identification. -/
def quotientPattern (F : Pattern) (rA : F.A → F.A → Prop) (rB : F.B → F.B → Prop) : Pattern where
  A := Quot rA
  B := Quot rB
  fintypeA := Fintype.ofFinite _
  fintypeB := Fintype.ofFinite _
  decEqA := Classical.decEq _
  decEqB := Classical.decEq _
  mult a b := ∑ x : F.A, ∑ y : F.B,
    if Quot.mk rA x = a ∧ Quot.mk rB y = b then F.mult x y else 0

def disjointPattern (F G : Pattern) : Pattern where
  A := F.A ⊕ G.A
  B := F.B ⊕ G.B
  mult a b := match a,b with
    | .inl x, .inl y => F.mult x y
    | .inr x, .inr y => G.mult x y
    | _, _ => 0

namespace BiPattern
variable {c : ℕ}
def compose (F G : BiPattern c) : BiPattern c :=
  let U := disjointPattern F.pattern G.pattern
  let rA : U.A → U.A → Prop := fun a b => ∃ s, a = .inl (F.outL s) ∧ b = .inr (G.inL s)
  let rB : U.B → U.B → Prop := fun a b => ∃ s, a = .inl (F.outR s) ∧ b = .inr (G.inR s)
  { pattern := quotientPattern U rA rB
    inL := fun s => Quot.mk rA (.inl (F.inL s))
    inR := fun s => Quot.mk rB (.inl (F.inR s))
    outL := fun s => Quot.mk rA (.inr (G.outL s))
    outR := fun s => Quot.mk rB (.inr (G.outR s)) }

def close (F : BiPattern c) : Pattern :=
  quotientPattern F.pattern
    (fun a b => ∃ s, a = F.inL s ∧ b = F.outL s)
    (fun a b => ∃ s, a = F.inR s ∧ b = F.outR s)

abbrev Assignment (c n : ℕ) := (Fin (c+1) ⊕ Fin (c+1)) → Fin n

def matrix (K : Type) [Field K] (F : BiPattern c) (n : ℕ) :
    Matrix (Assignment c n) (Assignment c n) (MvPolynomial (Fin n × Fin n) K) :=
  fun a b => ∑ hL : F.pattern.A → Fin n, ∑ hR : F.pattern.B → Fin n,
    if (∀ s, hL (F.inL s) = a (.inl s) ∧ hR (F.inR s) = a (.inr s) ∧
      hL (F.outL s) = b (.inl s) ∧ hR (F.outR s) = b (.inr s)) then
        ∏ x : F.pattern.A, ∏ y : F.pattern.B,
          (MvPolynomial.X (hL x,hR y)) ^ F.pattern.mult x y
    else 0
end BiPattern

inductive Atom (c : ℕ)
  | edge (s t : Fin (c+1))
  | resetL (s : Fin (c+1))
  | resetR (s : Fin (c+1))

def identityBi (c : ℕ) : BiPattern c where
  pattern := { A := Fin (c+1), B := Fin (c+1), mult := fun _ _ => 0 }
  inL := id
  inR := id
  outL := id
  outR := id

def atomBi {c : ℕ} : Atom c → BiPattern c
  | .edge s t =>
    { identityBi c with pattern :=
      { A := Fin (c+1), B := Fin (c+1), mult := fun a b => if a = s ∧ b = t then 1 else 0 } }
  | .resetL s =>
    { pattern := { A := Option (Fin (c+1)), B := Fin (c+1), mult := fun _ _ => 0 }
      inL := some, inR := id, outL := fun i => if i = s then none else some i, outR := id }
  | .resetR s =>
    { pattern := { A := Fin (c+1), B := Option (Fin (c+1)), mult := fun _ _ => 0 }
      inL := id, inR := some, outL := id, outR := fun i => if i = s then none else some i }

def wordBi {c : ℕ} (u : List (Atom c)) : BiPattern c :=
  u.foldl (fun F a => F.compose (atomBi a)) (identityBi c)

def patternIso (F G : Pattern) : Prop :=
  ∃ a : F.A ≃ G.A, ∃ b : F.B ≃ G.B, ∀ x y, G.mult (a x) (b y) = F.mult x y

def withIsolates (F : Pattern) (c : ℕ) : Pattern :=
  disjointPattern F (identityBi c).pattern

end SymmetricDepthHierarchy.ConstantDepth.Supplement


