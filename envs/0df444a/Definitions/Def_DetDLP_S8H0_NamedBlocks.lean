-- Prove2me | Definitions.Def_DetDLP_S8H0_NamedBlocks
-- name    : DetDLP_S8H0_NamedBlocks
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:11:37.389002+00:00
-- url     : https://prove2.me/theorems/56be34b0-ce50-46a9-a7fb-03258ef4d875
-- title:
--   Local tests on addressed register bits and public bits
-- statement:
--   Map an existing factor test to ports reading public bits, register bits or publicly masked register bits. Disjoint joins implement conjunction. Row tests and the fixed addition layout admit semantic descriptions on arbitrary Boolean assignments.
-- source:
--   Companion to DetDLP.s8h_ec_order_query, f0e81f0e-6143-4672-a126-0c2b5aa2d552.

import Definitions.Def_DetDLP_S8H0_AnchoredLayout
import Definitions.Def_DetDLP_S8H0_RegisterMap

set_option autoImplicit false
namespace DetDLP.S8H0.NamedBlocks
open S8J S8J.CircuitRealizes RegisterMap ResidueWires
attribute [-simp] Fin.natAdd_eq_addNat

/-- The last register is a dummy occurrence for a public bit. The port reader
    uses the supplied constant, and a separate unary predicate fixes the dummy. -/
inductive Ref (s : Shape) where
  | pin (v : Bool)
  | reg (a : Addr s)
  | masked (v : Bool) (a : Addr s)

def Ref.source {s} : Ref s → Fin (s.size+1)
  | .pin _ => Fin.last _
  | .reg a | .masked _ a => a.index.castSucc

def Ref.read {s} : Ref s → Bool → Bool
  | .pin v,_ => v
  | .reg _,b => b
  | .masked v _,b => v && b

def Ref.eval {s} (r : Ref s) (x : Fin (s.size+1) → Bool) := r.read (x r.source)

def Ref.data {s} : Ref s → s.Data → Bool
  | .pin v,_ => v
  | .reg a,x => a.get x
  | .masked v a,x => v && a.get x

theorem Ref.correct {s} (r : Ref s) (x : Fin (s.size+1) → Bool) :
    r.data (s.decode (x ∘ Fin.castSucc)) = r.eval x := by
  cases r <;> simp [data,eval,read,source,Addr.correct]

structure B (k : ℕ) where
  core : Block
  name : Fin core.A.ne → Fin k

def B.OK {k} (u : B k) (x : Fin k → Bool) := AnchoredLayout.Good u.core u.name x

def joinB {k} (u v : B k) : B k :=
  ⟨⟨join u.core.A v.core.A,joinTest u.core.t v.core.t⟩,Fin.addCases u.name v.name⟩

theorem joinB_iff {k} (u v : B k) (x : Fin k → Bool) : (joinB u v).OK x ↔ u.OK x ∧ v.OK x := by
  constructor
  · intro h
    exact ⟨fun g => by simpa [joinB,joinTest] using h (Fin.castAdd v.core.A.ng g),
      fun g => by simpa [joinB,joinTest] using h (Fin.natAdd u.core.A.ng g)⟩
  · rintro ⟨h,j⟩ g
    induction g using Fin.addCases with
    | left i => simpa [joinB,joinTest] using h i
    | right i => simpa [joinB,joinTest] using j i

def mapped {s : Shape} (A : w3_FactorLayout) (t : w3_factorTest A) (r : Fin A.nb → Ref s) : B (s.size+1) :=
  ⟨⟨A,fun g f => t g fun e => (r (A.bit e.val)).read (f e)⟩,fun e => (r (A.bit e)).source⟩

theorem mapped_iff {s : Shape} (A : w3_FactorLayout) (t : w3_factorTest A) (r : Fin A.nb → Ref s)
    (x : Fin (s.size+1) → Bool) : (mapped A t r).OK x ↔ Accept A t (fun i => (r i).eval x) := Iff.rfl

def rows {s : Shape} (n m : ℕ) (r : Fin n → Fin m → Ref s) (test : Fin n → (Fin m → Bool) → Bool) : B (s.size+1) :=
  let A : w3_FactorLayout := ⟨n,n*m,n*m,fun i => (finProdFinEquiv.symm i).1,id,id,fun _ => rfl⟩
  let t : w3_factorTest A := fun g x => test g (fun i => x ⟨finProdFinEquiv (g,i),by simp [A]⟩)
  mapped A t (fun i => r (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

theorem rows_iff {s : Shape} (n m : ℕ) (r : Fin n → Fin m → Ref s) (test : Fin n → (Fin m → Bool) → Bool)
    (x : Fin (s.size+1) → Bool) : (rows n m r test).OK x ↔ ∀ i, test i (fun j => (r i j).eval x) = true := by
  have h₁ (i : Fin n) (j : Fin m) : (finProdFinEquiv (i,j)).divNat = i := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i,j))
  have h₂ (i : Fin n) (j : Fin m) : (finProdFinEquiv (i,j)).modNat = j := congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i,j))
  simp [rows,mapped,B.OK,AnchoredLayout.Good,Ref.eval,h₁,h₂]

def eqs {s : Shape} (n : ℕ) (l r : Fin n → Ref s) := rows n 2 (fun i => ![l i,r i]) (fun _ a => decide (a 0 = a 1))

theorem eqs_iff {s : Shape} (n : ℕ) (l r : Fin n → Ref s) (x : Fin (s.size+1) → Bool) :
    (eqs n l r).OK x ↔ ∀ i, (l i).eval x = (r i).eval x := by simp [eqs,rows_iff]

def colRef {s : Shape} {n : ℕ} (a b z c : Fin n → Ref s) (k : Fin (n*4)) :=
  let i : Fin n := ⟨k.val/4,by omega⟩
  match k.val%4 with
  | 0 => a i | 1 => b i | 2 => z i | _ => c i

def add {s : Shape} {n : ℕ} (cin : Bool) (a b z c : Fin n → Ref s) :=
  mapped (S8C.AddLayout.layout n) (S8C.AddLayout.test cin) (colRef a b z c)

theorem add_iff {s : Shape} {n : ℕ} (cin : Bool) (a b z c : Fin n → Ref s) (x : Fin (s.size+1) → Bool) :
    (add cin a b z c).OK x ↔ S8C.AddLayout.Columns cin (fun i => (a i).eval x) (fun i => (b i).eval x)
      (fun i => (z i).eval x) (fun i => (c i).eval x) := by
  refine (S8C.AddLayout.test_iff cin (fun i => (colRef a b z c i).eval x)).trans ?_
  have hr (i : Fin n) (j : Fin 4) : (S8C.AddLayout.reg i j).val / 4 = i.val ∧ (S8C.AddLayout.reg i j).val % 4 = j.val := by simp only [S8C.AddLayout.reg]; omega
  simp only [colRef,(hr _ _).1,(hr _ _).2]; rfl

end DetDLP.S8H0.NamedBlocks


