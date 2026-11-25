-- Prove2me | Definitions.Def_DetDLP_S8G_FpMomentCert
-- name    : DetDLP_S8G_FpMomentCert
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:53:08.344945+00:00
-- url     : https://prove2.me/theorems/15cb7ebd-17c8-4b90-b983-8e47ac0a2082
-- title:
--   Unique certificates for prime-field moment witnesses
-- statement:
--   A checked hash run projects bijectively to a member of the corresponding factor block. Two modular product computations with a shared final residue certify collisions; each starts at its first factor.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8G_FpMomentCount
import Definitions.Def_DetDLP_S8C_FpQueryCount

set_option autoImplicit false
namespace DetDLP.S8G.FpMoment
open S8C

variable {p m : ℕ} [Fact p.Prime]
abbrev U (p : ℕ) := (ZMod p)ˣ

def atomsOK (S : FpSeed p m) (T : ℕ) (A : Fin m → U p) (r : Fin m → AtomRun p) :=
  ∀ i, atomOK S i T (w3_fpResidue (A i)) (r i)

/-- This equivalence is fiberwise in a variable seed, with no hardwired hash coefficients. -/
noncomputable def atomsEquiv (mul : w3_modMulInterface) (S : FpSeed p m) (T : ℕ) :
    {v : (Fin m → U p) × (Fin m → AtomRun p) // atomsOK S T v.1 v.2} ≃ Tuple (fpFactorBlock T S) := by
  apply certEquiv
  · intro A r hr
    exact Fintype.mem_piFinset.mpr fun i => atom_sound mul S i T _ _ (hr i)
  · intro A hA
    have hi := fun i => (atom_mem_iff mul S i T (A i)).mpr (Fintype.mem_piFinset.mp hA i)
    choose r hr hu using hi
    exact ⟨r,hr,fun s hs => funext fun i => hu i _ (hs i)⟩

def tailWords (A : Fin (m+1) → U p) := List.ofFn (fun i : Fin m => w3_fpResidue (A i.succ))

def chainOK (A : Fin (m+1) → U p) (z : Fin p) (r : ProductRun p) :=
  w3_checkStages (Nat.succ_pos (bitLen p)) (w3_fpResidue (A 0)) (tailWords A) r z

theorem chainValue (A : Fin (m+1) → U p) :
    ((w3_fpResidue (A 0)).val * ((tailWords A).map Fin.val).prod) % p = (w3_fpResidue (∏ i, A i)).val := by
  rw [← ZMod.val_natCast, Nat.cast_mul, Fin.prod_univ_succ]
  simp [tailWords, w3_fpResidue, List.map_ofFn, Function.comp_def, List.prod_ofFn, Units.coe_prod]

theorem chainSound (mul : w3_modMulInterface) (A : Fin (m+1) → U p) (z : Fin p) (r : ProductRun p)
    (hr : chainOK A z r) : z = w3_fpResidue (∏ i, A i) := Fin.ext
  ((w3_checkStages_output _ (Fact.out : p.Prime).two_le (primeFitsAtom p) mul _ _ _ _ hr).trans (chainValue A))

theorem chainUnique (mul : w3_modMulInterface) (A : Fin (m+1) → U p) :
    ∃! r, chainOK A (w3_fpResidue (∏ i, A i)) r :=
  w3_checkStages_existsUnique _ (Fact.out : p.Prime).two_le (primeFitsAtom p) mul _ _ _ (chainValue A).symm

theorem chainLength (A : Fin (m+1) → U p) (z : Fin p) (r : ProductRun p) (hr : chainOK A z r) :
    r.length = m := by
  suffices aux : ∀ (x : Fin p) ys (rs : ProductRun p), w3_checkStages (Nat.succ_pos (bitLen p)) x ys rs z →
      rs.length = ys.length by simpa [tailWords] using aux _ _ _ hr
  intro x ys
  induction ys generalizing x with
  | nil => rintro (_|_) h; exact rfl; exact False.elim h
  | cons a ys ih =>
    intro rs h
    cases rs with
    | nil => exact False.elim h
    | cons s rest => exact congrArg Nat.succ (ih s.1 rest h.2)

abbrev Checked (S : FpSeed p m) (T : ℕ) :=
  {v : (Fin m → U p) × (Fin m → AtomRun p) // atomsOK S T v.1 v.2}
abbrev Joined (S : FpSeed p (m+1)) (T : ℕ) :=
  {v : (Checked S T × Checked S T) × (Fin p × ProductRun p × ProductRun p) //
    chainOK v.1.1.val.1 v.2.1 v.2.2.1 ∧ chainOK v.1.2.val.1 v.2.1 v.2.2.2}

/-- Erase both hash transcripts and the two chains; the common residue and all runs are forced. -/
noncomputable def joinedEquiv (mul : w3_modMulInterface) (S : FpSeed p (m+1)) (T : ℕ) :
    Joined S T ≃ Collision (fpFactorBlock T S) := by
  let e := atomsEquiv mul S T
  let proj (a : Checked S T) : (e a).val = a.val.1 := rfl
  let toC (v : Joined S T) : Collision (fpFactorBlock T S) :=
    ⟨(e v.1.1.1, e v.1.1.2), by
      simp only [proj]
      have ha := chainSound mul _ _ _ v.2.1
      have hb := chainSound mul _ _ _ v.2.2
      exact Units.ext (ZMod.val_injective p (congrArg Fin.val (ha.symm.trans hb)))⟩
  apply Equiv.ofBijective toC
  constructor
  · rintro ⟨⟨⟨a,b⟩,z,r,s⟩,hr,hs⟩ ⟨⟨⟨a',b'⟩,z',r',s'⟩,hr',hs'⟩ h
    obtain rfl : a = a' := e.injective (congrArg (fun x => x.val.1) h)
    obtain rfl : b = b' := e.injective (congrArg (fun x => x.val.2) h)
    obtain rfl : z = z' := (chainSound mul _ _ _ hr).trans (chainSound mul _ _ _ hr').symm
    have ur := chainUnique mul a.val.1
    have us := chainUnique mul b.val.1
    rw [← chainSound mul _ _ _ hr] at ur
    rw [← chainSound mul _ _ _ hs] at us
    cases ur.unique hr hr'; cases us.unique hs hs'; rfl
  · rintro ⟨⟨a,b⟩,hab⟩
    let A := e.symm a
    let B := e.symm b
    have hA : A.val.1 = a.val := (proj A).symm.trans (congrArg Subtype.val (e.apply_symm_apply a))
    have hB : B.val.1 = b.val := (proj B).symm.trans (congrArg Subtype.val (e.apply_symm_apply b))
    obtain ⟨r,hr,_⟩ := chainUnique mul A.val.1
    obtain ⟨s,hs,_⟩ := chainUnique mul B.val.1
    have hAB : (∏ i, A.val.1 i) = ∏ i, B.val.1 i := by rw [hA,hB]; exact hab
    rw [← hAB] at hs
    exact ⟨⟨((A,B),_,r,s),hr,hs⟩,Subtype.ext (Prod.ext (e.apply_symm_apply a) (e.apply_symm_apply b))⟩

end DetDLP.S8G.FpMoment


