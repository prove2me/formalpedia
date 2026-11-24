-- Prove2me | Definitions.Def_ValiantBorder_groupEvaluator
-- name    : ValiantBorder_groupEvaluator
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:07:27.437788+00:00
-- url     : https://prove2.me/theorems/299423c4-2886-4acf-af40-19e8dc3c33e3
-- title:
--   Weighted evaluation of a group of tape segments
-- statement:
--   These data describe the evaluation of tape segments grouped according to exchange laws. They specify the boundary encoding, the weighted sum to be returned and the running time allowed for the evaluator.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Cuts.lean#L72).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Cuts.lean#L72.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_cutLaws
import Definitions.Def_ValiantBorder_tapeAutomata
/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026),
source `anthropics/formal-math` at `11b6c7e3c927df2658f513b6b68ea7f8929c62c5`.
The weighted evaluator, group instructions and resource estimates are from
`Nc/G/Defs.lean`, `Nc/Grp/{Script,GroupThm,GrpTime}.lean`, `Nc/Dl/{Inst,GrpCost}.lean`,
and `Paper/Cuts.lean`. Apache-2.0. -/
set_option linter.unusedSectionVars false
namespace NS1
open NS1.Tree
variable {A : Type} [CommRing A]
def listT : List Tree → Tree
  | [] => .nil
  | x :: xs => .cons x (listT xs)
inductive WE where
  
  | zero
  
  | one
  
  | nm (p : List Bool)
  
  | add (a b : WE)
  
  | mul (a b : WE)
def WE.val (θ : List Bool → A) : WE → A
  | zero => 0
  | one => 1
  | nm p => θ p
  | add a b => a.val θ + b.val θ
  | mul a b => a.val θ * b.val θ

end NS1

namespace Paper
open NS1
variable {A : Type} [CommRing A]
def Generates (θ : List Bool → A) : Prop := (Function.support θ).Finite ∧ ∀ a, ∃ w : WE, w.val θ = a

end Paper

namespace Nc
variable {A U : Type*} [DecidableEq A]
def Holds (h0 h1 : U → A) (a : A) (id : U) : Prop := a = h0 id ∨ a = h1 id
instance (h0 h1 : U → A) (a : A) (id : U) : Decidable (Holds h0 h1 a id) := by
  unfold Holds; infer_instance

end Nc

namespace Nc
open Finset
variable {F : Type*} [CommRing F] {A U W G : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

def cutUnits (h0 h1 : U → A) (grp : A → G) (Cur : Finset U) : Finset U :=
  Cur.filter fun id => grp (h0 id) ≠ grp (h1 id)
def GContents (h0 h1 : U → A) (e : W) (Seen : Finset U) (grp : A → G) (g : G) : Finset (A → U → W) :=
  univ.filter fun y => ∀ a id, ¬ (grp a = g ∧ id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e
structure GAgree (h0 h1 : U → A) (grp : A → G) (g : G) (Cur : Finset U) (b : U → W) (y : A → U → W) : Prop where
  both : ∀ id ∈ Cur, grp (h0 id) = g → grp (h1 id) = g → y (h0 id) id = y (h1 id) id
  fst : ∀ id ∈ Cur, grp (h0 id) = g → grp (h1 id) ≠ g → y (h0 id) id = b id
  snd : ∀ id ∈ Cur, grp (h0 id) ≠ g → grp (h1 id) = g → y (h1 id) id = b id
open Classical in
noncomputable def groupVal (h0 h1 : U → A) (e : W) (Seen Cur : Finset U) (grp : A → G) (φ : A → (U → W) → F)
    (g : G) (b : U → W) : F :=
  ∑ y ∈ GContents h0 h1 e Seen grp g, if GAgree h0 h1 grp g Cur b y then
    ∏ a ∈ univ.filter (fun a => grp a = g), φ a (y a) else 0

end Nc

namespace Nc
open Finset Classical
variable {F : Type*} [CommRing F] {Γ S J Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]

noncomputable def blockW (mu : Letter S J Γ → Matrix Q Q F) (T : ℕ) (q q' : Q) (v : Ch S J → List Γ) : F :=
  ∑ o : Fin T → Letter S J Γ, if emit (List.ofFn o) = v then ((List.ofFn o).map mu).prod q q' else 0
noncomputable def wordsLe (Γ : Type*) [Fintype Γ] (T : ℕ) : Finset (List Γ) :=
  (List.finite_length_le Γ T).toFinset

end Nc

namespace Nc
variable (ub : ℕ)
abbrev UW := Option (Fin ub → Bool)
def ucount (L : List Bool) : ℕ := L.length / ub + 1
def uword (L : List Bool) (k : ℕ) : Fin ub → Bool := fun b => (L ++ [true]).getD (k * ub + b) false
def unitsOf (L : List Bool) (k : ℕ) : UW ub := if k < ucount ub L then some (uword ub L k) else none

end Nc

namespace Nc
variable {Γ : Type*} {c : ℕ}
def bitsOf (cb : Γ → Fin c → Bool) (X : List Γ) : List Bool := X.flatMap fun a => List.ofFn (cb a)

end Nc

namespace Nc
variable {Γ : Type*} {K : ℕ}
def cat (A : Fin K → List Γ) : List Γ := (List.ofFn A).flatten

end Nc

namespace Nc.Cut

open Finset

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A K U0 E U1 : ℕ}

section Start

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T ub : ℕ) {c : ℕ} (cb : Option Γ → Fin c → Bool)


noncomputable def joinSeg (X : Option S → List Γ) : List (Option Γ) :=
  (univ : Finset (Option S)).toList.flatMap fun s => (X s).map some ++ [none]


noncomputable def strOf (X : Option S → List Γ) : List Bool := bitsOf cb (joinSeg X)



def vec (R C : Option S → Fin A → List Γ) : Ch S Unit → List Γ
  | .tp s b => if b then cat (C (some s)) else cat (R (some s))
  | .inp _ => cat (C none)

open Classical in


noncomputable def partyW (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (p : Fin (K + K))
    (R C : Option S → Fin (K + K) → List Γ) : F :=
  Fin.addCases (motive := fun _ => F)
    (fun κ => if ∀ b, R none b = [] then blockW mu T (q κ.castSucc) (q κ.succ) (vec R C) else 0)
    (fun κ => if (∀ s b, R (some s) b = []) ∧ (∀ s b, C s b = []) ∧ cat (R none) = x κ then 1 else 0) p



abbrev RowData (A : ℕ) := Bool × Fin A × Fin A


def RowOk (d : RowData A) (X : Fin A → List Γ) : Prop :=
  if d.1 then ∀ b, X b = [] else X d.2.1 ≠ [] ∧ X d.2.2 ≠ [] ∧ ∀ b, X b ≠ [] → d.2.1 ≤ b ∧ b ≤ d.2.2


def prevHi (ρ : Fin A → RowData A) (p : Fin A) : ℕ :=
  if h : p.1 = 0 then 0 else (ρ ⟨p.1 - 1, by omega⟩).2.2.1


def ValidRows (ρ : Option S → Fin A → RowData A) : Prop :=
  ∀ s p, if (ρ s p).1 then (ρ s p).2.1.1 = prevHi (ρ s) p ∧ (ρ s p).2.2.1 = prevHi (ρ s) p
    else prevHi (ρ s) p ≤ (ρ s p).2.1.1 ∧ (ρ s p).2.1 ≤ (ρ s p).2.2


def parts (ℓ : ℕ) (u : List Γ) (κ : Fin K) : List Γ := (u.drop (κ.1 * ℓ)).take ℓ

end Start

section Moves

variable {I : Type} {lam : ℕ} (lab : I → Fin lam → Bool)


def sideString {B : ℕ} (len : I → ℕ) (i : Fin B → I) (g : ∀ k, Fin (len (i k)) → Bool) : List Bool :=
  (List.ofFn fun k => List.ofFn (lab (i k)) ++ List.ofFn (g k)).flatten

end Moves

end Nc.Cut

namespace Nc


def uwBits {ub : ℕ} : UW ub → List Bool
  | none => []
  | some w => List.ofFn w

end Nc

namespace Nc.G
open Finset
namespace Law

variable {F : Type} [CommRing F] (L : Law F)


abbrev SlAt (p : L.Ro) := {e : L.Sl // L.a e = p ∨ L.b e = p}


abbrev CnAt (p : L.Ro) := {ν : L.Cn // L.c ν = p ∨ L.d ν = p}


def slEnd (e : L.Sl) (d : Bool) : L.Ro := if d then L.b e else L.a e


def cnEnd (ν : L.Cn) (d : Bool) : L.Ro := if d then L.d ν else L.c ν

end Law


structure Sys (F : Type) [CommRing F] (A E : ℕ) where
  
  kind : Fin E → Law F
  
  part : ∀ x, (kind x).Ro → Fin A
  inj : ∀ x, Function.Injective (part x)

namespace Sys

variable {F : Type} [CommRing F] {A E : ℕ} (M : Sys F A E)


abbrev R := Σ x, (M.kind x).Ro


abbrev Z := Σ x, (M.kind x).Sl


abbrev N := Σ x, (M.kind x).Cn


def rp (r : M.R) : Fin A := M.part r.1 r.2


def zr (z : M.Z) (d : Bool) : M.R := ⟨z.1, (M.kind z.1).slEnd z.2 d⟩


def nr (ν : M.N) (d : Bool) : M.R := ⟨ν.1, (M.kind ν.1).cnEnd ν.2 d⟩


def zp (z : M.Z) (d : Bool) : Fin A := M.rp (M.zr z d)


def np (ν : M.N) (d : Bool) : Fin A := M.rp (M.nr ν d)

end Sys



inductive Uid (A U0 : ℕ) (N : Type) (U1 : ℕ) where
  
  | init (a b : Fin A) (k : Fin U0)
  
  | new (ν : N) (k : Fin U1)
  deriving DecidableEq, Fintype

variable {F : Type} [CommRing F] {A A' E U0 U1 : ℕ} {N : Type} [Fintype N] [DecidableEq N]



def cparty (np : N → Bool → Fin (A + A')) : Uid A U0 N U1 → Bool → Fin (A + A')
  | .init a b _, d => Fin.castAdd A' (if d then b else a)
  | .new ν _, d => np ν d


def hold0 (np : N → Bool → Fin (A + A')) (id : Uid A U0 N U1) : Fin (A + A') := cparty np id false


def hold1 (np : N → Bool → Fin (A + A')) (id : Uid A U0 N U1) : Fin (A + A') := cparty np id true


noncomputable def allIds (A U0 : ℕ) (N : Type) [Fintype N] [DecidableEq N] (U1 : ℕ) : List (Uid A U0 N U1) :=
  (univ : Finset (Uid A U0 N U1)).toList


def unum : Uid A U0 N U1 → ℕ
  | .init _ _ k => k
  | .new _ k => k


def ucnt (n : Fin A → Fin A → Fin (U0 + 1)) (o : N → Fin U1) : Uid A U0 N U1 → ℕ
  | .init a b _ => n a b
  | .new ν _ => (o ν).1 + 1


def seen0 (n : Fin A → Fin A → Fin (U0 + 1)) : Finset (Uid A U0 N U1) :=
  univ.filter fun id => (match id with
    | .init a b k => decide (k.1 < (n a b).1)
    | .new _ _ => false) = true

section Moves

variable (M : Sys F (A + A') E) {ub : ℕ}


def newUnits (x : Fin E) (o : M.N → Fin U1) : Finset (Uid A U0 M.N U1) :=
  univ.filter fun id => (match id with
    | .init _ _ _ => false
    | .new ν k => decide (ν.1 = x ∧ k ≤ o ν)) = true


def slotBits (t : ℕ) (ids : List (Uid A U0 N U1)) (y : Uid A U0 N U1 → UW ub) : List Bool :=
  (ids.flatMap fun id => uwBits (y id)) ++ List.replicate ((t - ids.length) * ub) false


def chString {I : Type} {lam B : ℕ} (lb : I → Fin lam → Bool) (len : I → ℕ) (i : Fin B → I)
    (g : ∀ k, Fin (len (i k)) → Bool) : List Bool :=
  (List.ofFn fun k => List.ofFn (lb (i k)) ++ List.ofFn (g k)).flatten


def ChOk (ν : N) (J : ℕ) (str : List Bool) (y : Uid A U0 N U1 → UW ub) : Prop :=
  ucount ub str = J + 1 ∧ ∀ k : Fin U1, y (.new ν k) = unitsOf ub str k

open Classical in


noncomputable def role (x : Fin E) (p : (M.kind x).Ro) (t : ℕ)
    (ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)) (o : M.N → Fin U1)
    (y : Uid A U0 M.N U1 → UW ub) : F :=
  if ∀ e, ∀ id ∈ ids e, y id ≠ none then
    ∑ i : Fin (t * ub) → (M.kind x).I,
      ∑ g : ∀ k, ∀ ν : (M.kind x).CnAt p, Fin ((M.kind x).len (i k) ν) → Bool,
        if ∀ ν : (M.kind x).CnAt p, ChOk ⟨x, ν.1⟩ (o ⟨x, ν.1⟩).1
          (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) y
        then ∏ k : Fin (t * ub), (M.kind x).tab p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k) else 0
  else 0

end Moves

section Plans

variable (M : Sys F (A + A') E)



structure Plan (M : Sys F (A + A') E) (U0 U1 : ℕ) where
  
  cons : (Fin A → Fin A → Fin (U0 + 1)) → (M.N → Fin U1) → M.Z → Finset (Uid A U0 M.N U1)
  
  num : (Fin A → Fin A → Fin (U0 + 1)) → (M.N → Fin U1) → Fin E → ℕ
  
  good : (Fin A → Fin A → Fin (U0 + 1)) → (M.N → Fin U1) → Fin E → Prop

namespace Plan

variable {M} (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1)


def seenAt (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (x : ℕ) : Finset (Uid A U0 M.N U1) :=
  seen0 n ∪ (univ.filter fun x' : Fin E => x'.1 < x).biUnion fun x' => newUnits M x' o


def used (x : ℕ) : Finset (Uid A U0 M.N U1) :=
  (univ.filter fun z : M.Z => z.1.1 < x).biUnion fun z => P.cons n o z


def cur (x : ℕ) : Finset (Uid A U0 M.N U1) := seenAt n o x \ P.used n o x


def Poss (ub : ℕ) (x : Fin E) : Prop := ∃ ι : Fin (P.num n o x * ub) → (M.kind x).I, ∀ ν : (M.kind x).Cn,
  (o ⟨x, ν⟩).1 = (∑ k, ((M.kind x).lam + (M.kind x).len (ι k) ν)) / ub


structure Ok (cap : ℕ) : Prop where
  causal : ∀ n o o' z, (∀ ν : M.N, ν.1 < z.1 → o ν = o' ν) → P.cons n o z = P.cons n o' z
  causal' : ∀ n o o' x, (∀ ν : M.N, ν.1 < x → o ν = o' ν) → P.num n o x = P.num n o' x
  causal'' : ∀ n o o' x, (∀ ν : M.N, ν.1 ≤ x → o ν = o' ν) → (P.good n o x ↔ P.good n o' x)
  sub : ∀ n o z, P.cons n o z ⊆ P.cur n o z.1
  hold : ∀ n o z, ∀ id ∈ P.cons n o z,
    (hold0 M.np id = M.zp z false ∧ hold1 M.np id = M.zp z true) ∨
    (hold1 M.np id = M.zp z false ∧ hold0 M.np id = M.zp z true)
  disj : ∀ n o (x : Fin E) e e', e ≠ e' → Disjoint (P.cons n o ⟨x, e⟩) (P.cons n o ⟨x, e'⟩)
  card : ∀ n o z, (P.cons n o z).card ≤ P.num n o z.1
  cap : ∀ n o x, P.num n o x ≤ cap


noncomputable def ids (z : M.Z) : List (Uid A U0 M.N U1) :=
  (allIds A U0 M.N U1).filter fun id => id ∈ P.cons n o z

end Plan

variable {M} {ub : ℕ}


noncomputable def roleAt (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (r : M.R)
    (y : Uid A U0 M.N U1 → UW ub) : F :=
  role M r.1 r.2 (P.num n o r.1) (fun e => P.ids n o ⟨r.1, e.1⟩) o y


noncomputable def partyTab (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1)
    (init : (Uid A U0 M.N U1 → UW ub) → F) (a : Fin (A + A')) (y : Uid A U0 M.N U1 → UW ub) : F :=
  init y * ∏ r : M.R, if M.rp r = a then roleAt P n o r y else 1

end Plans

section Start

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K c ub : ℕ} (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool)

open Classical in

noncomputable def tabInit (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Cut.RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (p : Fin (K + K)) (y : Uid (K + K) U0 N U1 → UW ub) : F :=
  ∑ R ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
    ∑ C ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
      if (∀ s, Cut.RowOk (ρ s) (R s)) ∧ (∀ b, ucount ub (Cut.strOf cb fun s => R s b) = n p b ∧
          ∀ k : Fin U0, y (.init p b k) = unitsOf ub (Cut.strOf cb fun s => R s b) k) ∧
        (∀ b, ucount ub (Cut.strOf cb fun s => C s b) = n b p ∧
          ∀ k : Fin U0, y (.init b p k) = unitsOf ub (Cut.strOf cb fun s => C s b) k)
      then Cut.partyW mu T q x p R C else 0



noncomputable def tabFinal {M : Sys F (K + K + A') E}
    (P : Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → Cut.RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.N → Fin U1) (p : Fin (K + K + A')) : (Uid (K + K) U0 M.N U1 → UW ub) → F :=
  Fin.addCases (motive := fun _ => (Uid (K + K) U0 M.N U1 → UW ub) → F)
    (fun p => partyTab P n o (tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p) (Fin.castAdd A' p))
    (fun e => partyTab P n o (fun _ => 1) (Fin.natAdd (K + K) e)) p


noncomputable def grpVal {G : Type} [DecidableEq G] {M : Sys F (K + K + A') E}
    (P : Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → Cut.RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.N → Fin U1) (grp : Fin (K + K + A') → G) (g : G) (b : Uid (K + K) U0 M.N U1 → UW ub) : F :=
  groupVal (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o E) (P.cur n o E) grp
    (tabFinal mu T cb P q x ρ n o) g b

end Start

end Nc.G

namespace Nc.Grp
open Finset Nc.G Nc.Cut
variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c cap : ℕ} {Gr : Type} [DecidableEq Gr]
variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool)
  {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
  (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
  (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)

abbrev Cell (M : Sys F (K + K + A') E) (U0 U1 : ℕ) := Fin (K + K + A') × G.Uid (K + K) U0 M.N U1
def baseList : List (Fin (K + K)) := (List.finRange (K + K)).filter fun p => grp (Fin.castAdd A' p) = g
noncomputable def allRoles (M : Sys F (K + K + A') E) : List M.R := (List.finRange E).flatMap fun x =>
  (univ : Finset (M.kind x).Ro).toList.map (Sigma.mk x)
noncomputable def roleList (M : Sys F (K + K + A') E) : List M.R := (allRoles M).filter fun r => grp (M.rp r) = g

end Nc.Grp

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut




structure Body where
  
  flags : List (List ℕ)
  
  kR : List (List (List Bool))
  
  kC : List (List (List Bool))


inductive Ins where
  
  | block (q q' : ℕ) (B : Body)
  
  | input (part : List (List Bool)) (B : Body)
  
  | both (k k' : List Bool)
  
  | one (k w : List Bool)
  


  | role (j t : ℕ) (slots keys : List (List (List Bool)))


def keysT (l : List (List (List Bool))) : Tree := listT (l.map fun ks => listT (ks.map ofBits))

namespace Body


def tree (B : Body) : Tree :=
  .cons (listT (B.flags.map fun l => listT (l.map num))) (.cons (keysT B.kR) (keysT B.kC))

end Body

namespace Ins


def tree : Ins → Tree
  | block q q' B => .cons (num 0) (.cons (.cons (num q) (num q')) B.tree)
  | input part B => .cons (num 1) (.cons (listT (part.map ofBits)) B.tree)
  | both k k' => .cons (num 2) (.cons (ofBits k) (ofBits k'))
  | one k w => .cons (num 3) (.cons (ofBits k) (ofBits w))
  | role j t slots keys => .cons (num (4 + j)) (.cons (num t)
      (.cons (keysT slots) (keysT keys)))

end Ins


def scriptT (bT bub : List Bool) (l : List Ins) : Tree :=
  .cons (.cons (ofBits bT) (ofBits bub)) (listT (l.map Ins.tree))


def bval (w : List Bool) : ℕ := w.foldl (fun a b => 2 * a + b.toNat) 0


def rowFlag {A : ℕ} (d : RowData A) (b : Fin A) : ℕ :=
  if d.1 then 0 else if b = d.2.1 ∨ b = d.2.2 then 1 else if d.2.1 ≤ b ∧ b ≤ d.2.2 then 2 else 0

section group

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c : ℕ} {Gr : Type} [DecidableEq Gr]

variable (qn : Q → ℕ) (cb : Option Γ → Fin c → Bool) {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1)
  (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
  (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)
  (key : Cell M U0 U1 → List Bool) (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ)



noncomputable def bodyOf (p : Fin (K + K)) : Body where
  flags := (univ : Finset (Option S)).toList.map fun s => (List.ofFn fun b => rowFlag (ρ s p) b).reverse
  kR := List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n p b).1).map fun k =>
    key (Fin.castAdd A' p, .init p b k)
  kC := List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n b p).1).map fun k =>
    if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k)


noncomputable def baseIns (p : Fin (K + K)) : List Ins :=
  Fin.addCases (motive := fun _ => Ins)
    (fun κ => .block (qn (q κ.castSucc)) (qn (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
    (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p ::
  ((List.finRange U0).filter fun k => k.1 < (n p p).1).map fun k =>
    .both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))


noncomputable def roleIns (r : M.R) : Ins :=
  .role (tg r) (P.num n o r.1)
    ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)
    ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k))


noncomputable def endIns (b : G.Uid (K + K) U0 M.N U1 → UW ub) : List Ins :=
  ((G.allIds (K + K) U0 M.N U1).filter fun id => id ∈ P.cur n o E).filterMap fun id =>
    if grp (G.hold0 M.np id) = g then
      if grp (G.hold1 M.np id) = g then some (.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
      else some (.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
    else if grp (G.hold1 M.np id) = g then some (.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
    else none


noncomputable def script (b : G.Uid (K + K) U0 M.N U1 → UW ub) : List Ins :=
  (baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey) ++
  (roleList grp g M).map (roleIns P n o key tg) ++ endIns P n o grp g key b

end group

end Nc.Grp

namespace Nc.Grp

noncomputable def qn (Q : Type) [Fintype Q] : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q

end Nc.Grp

namespace Nc.Grp

def putCost (ub : ℕ) (kss : List (List (List Bool))) : ℕ :=
  (kss.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum
def flen (l : List (List ℕ)) : ℕ := (l.map List.length).sum
def bodyCost (ub : ℕ) (B : Body) : ℕ := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1
def insCost (T ub : ℕ) : Ins → ℕ
  | .block _ _ B => T + bodyCost ub B
  | .input part B => part.length + bodyCost ub B
  | .both k k' => k.length + k'.length + ub + 1
  | .one k w => k.length + w.length + ub + 1
  | .role _ tt slots keys => tt * (ub + 1) + putCost ub slots + putCost ub keys + 1

end Nc.Grp

namespace Nc.Dl

abbrev NN (K U0 : ℕ) := Fin (K + K) → Fin (K + K) → Fin (U0 + 1)

end Nc.Dl

namespace Nc.Dl
open NS1 NS1.Tree Finset Nc.G Nc.Cut
def grpT (bT bub : List Bool) (l : List Grp.Ins) : ℕ :=
  (bT.length + 1) * (Grp.bval bT + 1) + (bub.length + 1) * (Grp.bval bub + 1) +
    (l.map (Grp.insCost (Grp.bval bT) (Grp.bval bub))).sum + l.length
def GroupOK {A : Type} [CommRing A] (θ : List Bool → A) {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
    [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ} (mu : Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : G.Law A, L.Ro)) (qn : Q → ℕ) (GROUP : Fm) (κ : ℕ) : Prop :=
  ∀ {A' K E U0 U1 cap : ℕ} {Gr : Type} [DecidableEq Gr] [Fintype Gr]
    {M : Sys A (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr) (key : Grp.Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ) (bT bub : List Bool)
    (b : G.Uid (K + K) U0 M.N U1 → UW (Grp.bval bub)),
    Function.Injective (Sum.elim key dkey) → 0 < Grp.bval bub → P.Ok cap → (∀ κ, (x κ).length ≤ Grp.bval bT) →
    (∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) → (∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩) →
    Plain θ (κ * grpT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))
      (.cons GROUP.code (Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))) ∧
    pv θ (.cons GROUP.code (Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))) =
      G.grpVal mu (Grp.bval bT) cb P q x ρ n o grp g b ∧
    (evl θ GROUP (Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b)) ≠ [] →
      (∀ p, grp (Fin.castAdd A' p) = g → ∑ b, ((n p b : ℕ) + n b p) ≤
        2 * ((Grp.bval bT + (K + K) * (Fintype.card S + 1)) * c / Grp.bval bub + (K + K))) ∧
      ∀ r : M.R, grp (M.rp r) = g → ∃ ι : Fin (P.num n o r.1 * Grp.bval bub) → (M.kind r.1).I,
        ∀ ν : (M.kind r.1).CnAt r.2,
          (o ⟨r.1, ν.1⟩ : ℕ) = (∑ k, ((M.kind r.1).lam + (M.kind r.1).len (ι k) ν.1)) / Grp.bval bub)

end Nc.Dl

namespace Nc.Dl

open Finset Nc.G

variable {A : Type} [CommRing A] {K A' E U0 U1 mm : ℕ} {M : Sys A (K + K + A') E}

open Classical in

noncomputable def evG (grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm) (n : NN K U0) (o : M.N → Fin U1)
    (g : Fin mm) : ℕ :=
  ∑ p ∈ univ.filter (fun p => grp n o p = g),
    ((Plan.seenAt n o E : Finset (Uid (K + K) U0 M.N U1)).filter (Holds (hold0 M.np) (hold1 M.np) p)).card

open Classical in

noncomputable def pdG (P : G.Plan M U0 U1) (grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm) (n : NN K U0)
    (o : M.N → Fin U1) (g : Fin mm) : ℕ :=
  ∑ r ∈ univ.filter (fun r : M.R => grp n o (M.rp r) = g),
    (1 + Fintype.card ((M.kind r.1).SlAt r.2)) * P.num n o r.1

end Nc.Dl

namespace Nc.Dl
open NS1 NS1.Tree Finset Nc.G Nc.Cut
def GrpTimeOK (A : Type) [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
    [DecidableEq Q] {c : ℕ} (cb : Option Γ → Fin c → Bool) (qn : Q → ℕ) : Prop :=
  ∀ {K A' E U0 U1 cap mm : ℕ} {M : Sys A (K + K + A') E} (P : G.Plan M U0 U1) (_ : P.Ok cap) (q : Fin (K + 1) → Q)
    (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
    (grp : Fin (K + K + A') → Fin mm) (g : Fin mm) (key : Grp.Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ) (bT bub : List Bool)
    (b : G.Uid (K + K) U0 M.N U1 → UW (Grp.bval bub)) {Lc X ιb lh ev : ℕ},
    (∀ κ, (x κ).length ≤ Grp.bval bT) → (∀ a, (key a).length ≤ Lc) → (∀ a, (dkey a).length ≤ Lc) → bT.length ≤ Lc →
    bub.length ≤ Lc → Fintype.card (Option S) ≤ X → K + K + 1 ≤ X → Fintype.card M.R ≤ X →
    Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X → (∀ y, Fintype.card (M.kind y).Sl ≤ X) →
    (∀ y, Fintype.card (M.kind y).Cn ≤ X) →
    (univ.filter fun p : Fin (K + K) => grp (Fin.castAdd A' p) = g).card ≤ ιb → ιb ≤ X →
    (∀ p : Fin (K + K), grp (Fin.castAdd A' p) = g → ∑ b, ((n p b).val + (n b p).val) ≤ lh) →
    evG (fun _ _ => grp) n o g + pdG P (fun _ _ => grp) n o g ≤ ev →
    grpT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b) ≤
      2 * (Lc + 1) * (Grp.bval bT + Grp.bval bub + 2) + ιb * Grp.bval bT +
      1000 * (ev + ιb * lh) * (Grp.bval bub + Lc + 1) + X ^ 4 * 1000 * (Lc + 1)

end Nc.Dl


