-- Prove2me | Definitions.Def_DetDLP_S8L_FpPairPhysicalHash
-- name    : DetDLP_S8L_FpPairPhysicalHash
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:07:27.305154+00:00
-- url     : https://prove2.me/theorems/db1737b2-257b-43e5-9a70-a8721e8f1374
-- title:
--   Physical witnesses for an affine hash atom
-- statement:
--   For a strict modulus, the modular multiplication stage followed by two column adders represents an affine hash certificate. Each valid certificate determines one physical assignment, including both carry strings.

import Definitions.Def_DetDLP_S8L_FpPairStageLinks
import Definitions.Def_DetDLP_S8L_FpPairChain

set_option autoImplicit false
namespace DetDLP.S8L.FpPair.PhysicalHash
open Stage Stage.Links S8C S8J

/-- Physical multiplier wires, the one-bit reduction flag, the full sum, and both carry strings. -/
abbrev Witness (d p : ℕ) (hd : 1 ≤ d) := Fin p × StageBits hd × Bool × Fin (2^(d+1)) × Vec (d+1) × Vec (d+1)
def project {d p : ℕ} (hd : 1 ≤ d) (v : Witness d p hd) : w3_fpHashCert d p hd :=
  ((v.1,certificate hd v.2.1),v.2.2.1)

def OK {d p : ℕ} (hd : 1 ≤ d) (a b x z : ℕ) (v : Witness d p hd) :=
  (Accept (layout hd) (linkedTests hd) v.2.1 ∧ Boundary hd p a x v.1.val v.2.1) ∧
  w3_addColumns (d+1) v.1.val b v.2.2.2.1.val false v.2.2.2.2.1 ∧
  w3_addColumns (d+1) z (if v.2.2.1 then p else 0) v.2.2.2.1.val false v.2.2.2.2.2

private theorem within {d p : ℕ} (hd : 1 ≤ d) (hp : p < 2^d) (u : Fin p) : u.val < 2^(2*d) :=
  (u.isLt.trans hp).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

variable {d p a b x z : ℕ} (hd : 1 ≤ d) (hp : p < 2^d) (hb : b < p) (hz : z < p)

private theorem broad (h : p < 2^d) : p < 2^(d+1) := by rw [pow_succ]; omega
include hp
private theorem multiple (f : Bool) : (if f then p else 0) < 2^(d+1) := by
  cases f <;> simp [broad hp]

include hb hz
theorem sound {v : Witness d p hd} (hv : OK hd a b x z v) : w3_fpHashCheck hd a b x z (project hd v) := by
  obtain ⟨h,l,r⟩ := hv
  obtain ⟨ht,hw⟩ := (linked_iff _ _ _ _ _ _).mp h
  have hl := w3_addColumns_sound (v.1.isLt.trans (broad hp)) (hb.trans (broad hp)) v.2.2.2.1.isLt l
  have hr := w3_addColumns_sound (hz.trans (broad hp)) (multiple hp _) v.2.2.2.1.isLt r
  refine ⟨decode hd (within hd hp _) _ ht hw,?_⟩
  change v.1.val+b = z+(if v.2.2.1 then p else 0)
  simp only [Bool.toNat_false,Nat.add_zero] at hl hr
  exact hl.trans hr.symm

theorem uniqueLift {r : w3_fpHashCert d p hd} (hr : w3_fpHashCheck hd a b x z r) :
    ∃! v : Witness d p hd, OK hd a b x z v ∧ project hd v = r := by
  rcases r with ⟨⟨u,r⟩,f⟩
  obtain ⟨hm,he⟩ := hr
  obtain ⟨v,hv,hv'⟩ := lift hd (within hd hp u) hm
  have hvb := (linked_iff _ _ _ _ _ _).mpr hv
  let s : Fin (2^(d+1)) := ⟨u.val+b,by rw [pow_succ]; have := u.isLt; omega⟩
  obtain ⟨l,hl,ul⟩ := w3_addColumns_unique (u.isLt.trans (broad hp)) (hb.trans (broad hp)) s.isLt
    (cin := false) (by simp [s])
  obtain ⟨k,hk,uk⟩ := w3_addColumns_unique (hz.trans (broad hp)) (multiple hp f) s.isLt
    (cin := false) (by simpa [s] using he.symm)
  refine ⟨(u,v,f,s,l,k),⟨⟨hvb,hl,hk⟩,by simp [project,hv']⟩,?_⟩
  rintro ⟨u',v',f',s',l',k'⟩ ⟨⟨hv'',hl',hk'⟩,heq⟩
  change ((u',certificate hd v'),f') = ((u,r),f) at heq
  obtain ⟨euf,ef⟩ := Prod.mk.inj heq; obtain ⟨eu,er⟩ := Prod.mk.inj euf
  subst u'; subst f'
  have ev := inject hd (within hd hp u) ((linked_iff _ _ _ _ _ _).mp hv'') hv (er.trans hv'.symm)
  have es : s' = s := Fin.ext (by simpa [s] using (w3_addColumns_sound (u.isLt.trans (broad hp)) (hb.trans (broad hp)) s'.isLt hl').symm)
  change v' = v at ev
  subst s'; subst v'
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext (ul _ hl') (uk _ hk')))))

noncomputable def equiv : {v : Witness d p hd // OK hd a b x z v} ≃ {r : w3_fpHashCert d p hd // w3_fpHashCheck hd a b x z r} := by
  apply Equiv.ofBijective (fun v => ⟨project hd v.1,sound hd hp hb hz v.2⟩)
  constructor
  · intro v w he
    have heq : project hd v.1 = project hd w.1 := congrArg Subtype.val he
    exact Subtype.ext ((uniqueLift hd hp hb hz (sound hd hp hb hz w.2)).unique ⟨v.2,heq⟩ ⟨w.2,rfl⟩)
  · intro r; obtain ⟨w,⟨hw,eq⟩,_⟩ := uniqueLift hd hp hb hz r.2; exact ⟨⟨w,hw⟩,Subtype.ext eq⟩

end DetDLP.S8L.FpPair.PhysicalHash


