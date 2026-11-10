-- Prove2me | Definitions.Def_HighPrecSAC1_Main_Quadratic
-- name    : HighPrecSAC1_Main_Quadratic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:24:00.876552+00:00
-- url     : https://prove2.me/theorems/568a708f-1b5a-4663-9888-62e2075718da
-- title:
--   Layered quadratic maps, monomial occurrences and circuit layering
-- statement:
--   A quadratic map is a list of constant, linear and quadratic monomial occurrences in each coordinate; repeated occurrences remain separate. Evaluation and Jacobians are explicit finite sums. A layered system consists of its initial vector and successive layer maps. The global map, its quadratic part and Jacobians are defined from those layers, and the exact fixed point is obtained by forward layer evaluation. Positivity is a separate predicate on the initial values and coefficients. The copy-per-layer construction is defined directly from the arithmetic circuit, and ordered Jacobian products are explicit.
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Definitions and constructions, §§2, 3, 6, 7, printed p. 13 (PDF 14)

import Definitions.Def_HighPrecSAC1_Main_Arithmetic

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

abbrev Vec (m : ℕ) := Fin m → ℝ
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℝ

/-- Monomial occurrences, preserving repeated wires rather than collecting coefficients. -/
inductive QTerm (m : ℕ) where
  | const (a : ℝ)
  | lin (a : ℝ) (j : Fin m)
  | quad (a : ℝ) (j k : Fin m)

noncomputable def QTerm.eval {m : ℕ} (z : Vec m) : QTerm m → ℝ
  | .const a => a
  | .lin a j => a * z j
  | .quad a j k => a * z j * z k

def QTerm.coeff {m : ℕ} : QTerm m → ℝ
  | .const a | .lin a _ | .quad a _ _ => a

noncomputable def QTerm.deriv {m : ℕ} (z : Vec m) (i : Fin m) : QTerm m → ℝ
  | .const _ => 0
  | .lin a j => if j = i then a else 0
  | .quad a j k => (if j = i then a*z k else 0) + (if k = i then a*z j else 0)

abbrev QuadMap (m : ℕ) := Fin m → List (QTerm m)

noncomputable def QuadMap.eval {m : ℕ} (P : QuadMap m) (z : Vec m) : Vec m :=
  fun i => ((P i).map (QTerm.eval z)).sum
noncomputable def QuadMap.jac {m : ℕ} (P : QuadMap m) (z : Vec m) : Mat m :=
  fun i j => ((P i).map (QTerm.deriv z j)).sum

def QuadMap.positive {m : ℕ} (P : QuadMap m) : Prop :=
  ∀ i a, a ∈ P i → 0 ≤ a.coeff

def QuadMap.quadratic {m : ℕ} (P : QuadMap m) : QuadMap m :=
  fun i => (P i).filter fun a => match a with | .quad _ _ _ => true | _ => false

/-- A concrete layered positive quadratic system, before the positivity restriction. -/
structure LayerSystem (K m : ℕ) where
  initial : Vec m
  layer : Fin K → QuadMap m

noncomputable def LayerSystem.at {K m : ℕ} (S : LayerSystem K m) (i : ℕ) : QuadMap m :=
  if h : 0 < i ∧ i ≤ K then S.layer ⟨i-1, by omega⟩ else fun _ => []

def LayerSystem.positive {K m : ℕ} (S : LayerSystem K m) : Prop :=
  0 ≤ S.initial ∧ ∀ i, (S.layer i).positive

noncomputable def LayerSystem.values {K m : ℕ} (S : LayerSystem K m) : ℕ → Vec m
  | 0 => S.initial
  | i+1 => (S.at (i+1)).eval (S.values i)

abbrev Coord (K m : ℕ) := Fin (K+1) × Fin m
abbrev GVec (K m : ℕ) := Coord K m → ℝ
abbrev GMat (K m : ℕ) := Matrix (Coord K m) (Coord K m) ℝ

/-- Entrywise matrix order, never the positive-semidefinite order. -/
def EntryLE {K m : ℕ} (A B : GMat K m) : Prop := ∀ v w, A v w ≤ B v w

noncomputable def LayerSystem.exact {K m : ℕ} (S : LayerSystem K m) : GVec K m :=
  fun v => S.values v.1.val v.2

noncomputable def LayerSystem.global {K m : ℕ} (S : LayerSystem K m) (z : GVec K m) : GVec K m :=
  fun v => if h : v.1.val = 0 then S.initial v.2 else
    (S.at v.1.val).eval (fun j => z (⟨v.1.val-1, by omega⟩,j)) v.2

noncomputable def LayerSystem.jac {K m : ℕ} (S : LayerSystem K m) (z : GVec K m) : GMat K m :=
  fun v w => if v.1.val = w.1.val+1 then
    (S.at v.1.val).jac (fun j => z (w.1,j)) v.2 w.2 else 0

noncomputable def LayerSystem.quad {K m : ℕ} (S : LayerSystem K m) (z : GVec K m) : GVec K m :=
  fun v => if h : v.1.val = 0 then 0 else
    (S.at v.1.val).quadratic.eval (fun j => z (⟨v.1.val-1, by omega⟩,j)) v.2

noncomputable def LayerSystem.dQuad {K m : ℕ} (S : LayerSystem K m) (z : GVec K m) : GMat K m :=
  fun v w => if v.1.val = w.1.val+1 then
    (S.at v.1.val).quadratic.jac (fun j => z (w.1,j)) v.2 w.2 else 0

/-- Copy-per-layer construction of §3.2. Source gates copy themselves; all other gates
    start at zero and subsequently read the previous layer. -/
noncomputable def layered {n : ℕ} (G : PositiveCircuit n) (K : ℕ) (x : Fin n → Bool) :
    LayerSystem K G.gates where
  initial := fun v => match G.gate v with
    | .atom a => Literal.value x a
    | _ => 0
  layer := fun _ v => match G.gate v with
    | .atom _ => [.lin 1 v]
    | .add xs => xs.map fun j => .lin 1 ⟨j.val, j.isLt.trans v.isLt⟩
    | .mul j k => [.quad 1 ⟨j.val, j.isLt.trans v.isLt⟩ ⟨k.val, k.isLt.trans v.isLt⟩]

/-- Ordered Jacobian product J_k ... J_(i+1). -/
noncomputable def propagate {m : ℕ} (J : ℕ → Mat m) (i : ℕ) : ℕ → Mat m
  | 0 => 1
  | d+1 => J (i+d+1) * propagate J i d

end HighPrecSAC1.Main


