-- Prove2me | Definitions.Def_dusart_theta_mesh_soundness
-- name    : dusart_theta_mesh_soundness
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:42:37.979991+00:00
-- url     : https://prove2.me/theorems/dca2e163-d4a9-4108-a61b-1a0602172427
-- title:
--   Dusart finite mesh:
-- statement:
--   The  component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric
import Definitions.Def_axler_theta_chain_base
import Mathlib.Tactic
namespace DusartMeshUpper.Literal
open RosserBitSieve
def Valid (len : ℕ) (ps : List (ℕ × ℕ)) : Prop :=
  ∀ dm ∈ ps, 2 ≤ dm.1 ∧ dm.2=periodicMask dm.1 ((len+dm.1-1)/dm.1)
lemma eq_pairs {len : ℕ} {ps : List (ℕ × ℕ)} (hv : Valid len ps) :
    ps=RosserCachedSieve.pairs len (ps.map Prod.fst) := by
  induction ps with
  | nil => rfl
  | cons dm ps ih =>
    have hm := hv dm (by simp)
    have ht : Valid len ps := by intro q hq; exact hv q (by simp [hq])
    simp only [RosserCachedSieve.pairs,List.map_cons,List.cons.injEq]
    exact ⟨by ext <;> simp [hm.2],ih ht⟩
def Spec (a b u v : ℕ) : Prop :=
  (1000000 : ℝ)*Chebyshev.theta (a : ℝ) ≤ u →
    (1000000 : ℝ)*Chebyshev.theta (b : ℝ) ≤ v ∧
    ∀ x : ℝ, (a : ℝ) ≤ x → x < (b : ℝ) → Chebyshev.theta x ≤ x+100000+x/10000
lemma compose {a b c u v w : ℕ} (h1 : Spec a b u v) (h2 : Spec b c v w) : Spec a c u w := by
  intro hstart
  obtain ⟨hb,hx1⟩ := h1 hstart
  obtain ⟨hc,hx2⟩ := h2 hb
  refine ⟨hc,?_⟩
  intro x hx hX
  by_cases hxb : x<(b : ℝ)
  · exact hx1 x hx hxb
  · exact hx2 x (le_of_not_gt hxb) hX
end DusartMeshUpper.Literal
namespace DusartMeshUpper.WordWitness
open RosserScan
def word : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
 | 0,_,base,cand,h => Nat.beq h 0 && Nat.beq (Nat.land base cand) base
 | fuel+1,a,base,cand,h => if h=0 then Nat.beq (Nat.land base cand) base else
   Nat.beq (Nat.mod (Nat.add (Nat.add a 1) (Nat.mod h 64))
     (Nat.add 2 (Nat.mod (Nat.div h 64) 131072))) 0 &&
   forceNat (Nat.lor cand (Nat.shiftLeft 1 (Nat.mod h 64))) fun cn =>
   word fuel a base cn (Nat.div h 8388608)
lemma word_cover (fuel a base cand hints i : ℕ) (ha : 131073≤a)
 (hc : word fuel a base cand hints=true) (hp : Nat.Prime (a+1+i))
 (hb : base.testBit i=true) : cand.testBit i=true := by
 induction fuel generalizing cand hints with
 | zero =>
   simp only [word,Bool.and_eq_true,Nat.beq_eq] at hc
   have h := congrArg (fun x : ℕ => x.testBit i) hc.2
   change (base &&& cand).testBit i=base.testBit i at h
   simpa only [Nat.testBit_and,hb,Bool.true_and] using h
 | succ fuel ih =>
   by_cases hz : hints=0
   · simp only [word,hz,if_true,Nat.beq_eq] at hc
     have h := congrArg (fun x : ℕ => x.testBit i) hc
     change (base &&& cand).testBit i=base.testBit i at h
     simpa only [Nat.testBit_and,hb,Bool.true_and] using h
   simp only [word,if_neg hz,forceNat_eq,Bool.and_eq_true,Nat.beq_eq] at hc
   let d := 2+(hints/64)%131072
   have hd2 : 2≤d := by dsimp only [d]; omega
   have hda : d≤a := by
     have hm := Nat.mod_lt (hints/64) (by decide : 0<131072)
     dsimp only [d]
     omega
   have hne : hints%64≠i := by
     intro he
     have hdvd : d∣a+1+i := by
       apply Nat.dvd_of_mod_eq_zero
       have hmod : (a+1+hints%64)%d=0 := hc.1
       simpa only [he] using hmod
     rcases hp.eq_one_or_self_of_dvd d hdvd with h|h <;> omega
   have hs : (1 <<< (hints%64)).testBit i=false := by
     rw [Nat.shiftLeft_eq,one_mul]
     exact Nat.testBit_two_pow_of_ne hne
   have h := ih (cand:=cand ||| (1 <<< (hints%64))) (hints:=hints/8388608) hc.2
   simpa only [Nat.testBit_or,hs,Bool.or_false] using h
lemma prime_card_le_mask (a b depth mask : ℕ) (hab : a<b)
 (hm : mask<2^(b-a)) (hdepth : b-a≤2^(depth+3))
 (hcover : ∀p, Nat.Prime p → a<p → p≤b → mask.testBit (p-(a+1))=true) :
 ((Nat.primesLE b).filter (fun p => a<p)).card≤AxlerTheta.bitCount depth mask := by
 rw [AxlerTheta.bitCount_sound depth mask (b-a) hm hdepth]
 rw [RosserPackedBarrier.candidateCount,←List.toFinset_card_of_nodup
  ((List.nodup_range (n:=b-a)).filter (fun i => mask.testBit i)),List.toFinset_filter,List.toFinset_range]
 apply Finset.card_le_card_of_injOn (fun p => p-(a+1))
 · intro p hp
   have hpa := (Finset.mem_filter.mp hp).2
   have hpb := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
   have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
   apply Finset.mem_filter.mpr
   exact ⟨Finset.mem_range.mpr (by change p-(a+1)<b-a; omega),hcover p hprime hpa hpb⟩
 · intro p hp q hq hpq
   have hpa := (Finset.mem_filter.mp hp).2
   have hqa := (Finset.mem_filter.mp hq).2
   change p-(a+1)=q-(a+1) at hpq
   omega
lemma theta_upper (a b depth mask : ℕ) (ha : 1≤a) (hab : a<b) (hb : b<2^64)
 (hm : mask<2^(b-a)) (hdepth : b-a≤2^(depth+3))
 (hcover : ∀p, Nat.Prime p → a<p → p≤b → mask.testBit (p-(a+1))=true) :
 (1000000 : ℝ)*(Chebyshev.theta (b : ℝ)-Chebyshev.theta (a : ℝ))≤
   (AxlerTheta.bitCount depth mask : ℝ)*(AxlerTheta.logUpNum b : ℝ) := by
 have ht := AxlerChain.theta_up_card ha hab hb
 have hc := prime_card_le_mask a b depth mask hab hm hdepth hcover
 have hc' : (((Nat.primesLE b).filter (fun p => a<p)).card : ℝ)≤
   (AxlerTheta.bitCount depth mask : ℝ) := by exact_mod_cast hc
 exact ht.trans (mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg _))
end DusartMeshUpper.WordWitness
namespace DusartMeshUpper.PackedWords
open RosserScan
def payload (h : ℕ) : ℕ := (h/128)%2^(23*(h%128))
def rest (h : ℕ) : ℕ := h/2^(7+23*(h%128))
def inner : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
 | 0,_,_,_,_ => true
 | n+1,a,base,cand,h =>
   forceNat (base%2^64) fun bw =>
   forceNat (cand%2^64) fun cw =>
   forceNat (payload h) fun hw =>
   WordWitness.word 64 a bw cw hw &&
   forceNat (base/2^64) fun bn =>
   forceNat (cand/2^64) fun cn =>
   forceNat (rest h) fun hn =>
   forceNat (a+64) fun an => inner n an bn cn hn
def check : ℕ → ℕ → ℕ → ℕ → List ℕ → Bool
 | 0,_,_,_,_ => true
 | _+1,_,_,_,[] => false
 | n+1,a,base,cand,h::hs =>
   forceNat (base%2^2048) fun bw =>
   forceNat (cand%2^2048) fun cw =>
   inner 32 a bw cw h &&
   forceNat (base/2^2048) fun bn =>
   forceNat (cand/2^2048) fun cn =>
   forceNat (a+2048) fun an => check n an bn cn hs
lemma inner_cover (n a base cand h i : ℕ) (ha : 131073≤a)
 (hc : inner n a base cand h=true) (hi : i<64*n)
 (hp : Nat.Prime (a+1+i)) (hb : base.testBit i=true) : cand.testBit i=true := by
 induction n generalizing a base cand h i with
 | zero => omega
 | succ n ih =>
   simp only [inner,forceNat_eq,Bool.and_eq_true] at hc
   by_cases hw : i<64
   · have hb' : (base%2^64).testBit i=true := by
       simp only [Nat.testBit_mod_two_pow,hw,decide_true,Bool.true_and,hb]
     have hr := WordWitness.word_cover 64 a (base%2^64) (cand%2^64) (payload h) i ha hc.1 hp hb'
     simpa only [Nat.testBit_mod_two_pow,hw,decide_true,Bool.true_and] using hr
   · have he : (i-64)+64=i := by omega
     have hi' : i-64<64*n := by omega
     have hp' : Nat.Prime ((a+64)+1+(i-64)) := by
       have he' : (a+64)+1+(i-64)=a+1+i := by omega
       simpa only [he'] using hp
     have hb' : (base/2^64).testBit (i-64)=true := by
       simpa only [Nat.testBit_div_two_pow,he] using hb
     have hr := ih (a:=a+64) (base:=base/2^64) (cand:=cand/2^64) (h:=rest h) (i:=i-64)
       (by omega) hc.2 hi' hp' hb'
     simpa only [Nat.testBit_div_two_pow,he] using hr
lemma check_cover (n a base cand : ℕ) (hints : List ℕ) (ha : 131073≤a)
 (hc : check n a base cand hints=true) (i : ℕ) (hi : i<2048*n)
 (hp : Nat.Prime (a+1+i)) (hb : base.testBit i=true) : cand.testBit i=true := by
 induction n generalizing a base cand hints i with
 | zero => omega
 | succ n ih =>
   cases hints with
   | nil => simp only [check,Bool.false_eq_true] at hc
   | cons h hs =>
     simp only [check,forceNat_eq,Bool.and_eq_true] at hc
     by_cases hw : i<2048
     · have hb' : (base%2^2048).testBit i=true := by
         simp only [Nat.testBit_mod_two_pow,hw,decide_true,Bool.true_and,hb]
       have hr := inner_cover 32 a (base%2^2048) (cand%2^2048) h i ha hc.1 (by omega) hp hb'
       simpa only [Nat.testBit_mod_two_pow,hw,decide_true,Bool.true_and] using hr
     · have he : (i-2048)+2048=i := by omega
       have hi' : i-2048<2048*n := by omega
       have hp' : Nat.Prime ((a+2048)+1+(i-2048)) := by
         have he' : (a+2048)+1+(i-2048)=a+1+i := by omega
         simpa only [he'] using hp
       have hb' : (base/2^2048).testBit (i-2048)=true := by
         simpa only [Nat.testBit_div_two_pow,he] using hb
       have hr := ih (a:=a+2048) (base:=base/2^2048) (cand:=cand/2^2048) (hints:=hs)
         (by omega) hc.2 (i-2048) hi' hp' hb'
       simpa only [Nat.testBit_div_two_pow,he] using hr
lemma interval_cover (groups a b base cand : ℕ) (hints : List ℕ)
 (ha : 131073≤a) (hlen : b-a≤2048*groups) (hc : check groups a base cand hints=true)
 (hbase : ∀p, Nat.Prime p → a<p → p≤b → base.testBit (p-(a+1))=true) :
 ∀p, Nat.Prime p → a<p → p≤b → cand.testBit (p-(a+1))=true := by
 intro p hp hpa hpb
 apply check_cover groups a base cand hints ha hc (p-(a+1)) (by omega)
 · have he : a+1+(p-(a+1))=p := by omega
   simpa only [he] using hp
 · exact hbase p hp hpa hpb
end DusartMeshUpper.PackedWords
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace DusartNumericBridge
open DusartMeshUpper
lemma force_apply {α : Type} (n : Nat) (f : Nat → α) : DusartNumeric.forceNat n f=f n := by cases n <;> rfl
lemma bytes_eq (mask stripe j total : Nat) : DusartNumeric.countBytes mask stripe j total=AxlerTheta.countBytes mask stripe j total := by
 induction j generalizing total with
 | zero => rfl
 | succ j ih => simp only [DusartNumeric.countBytes,AxlerTheta.countBytes,force_apply,RosserScan.forceNat_eq,ih]
lemma combine_eq (bits half count : Nat) : DusartNumeric.countCombine bits half count=AxlerTheta.countCombine bits half count := by rfl
lemma reduce_eq (bits fuel half total : Nat) : DusartNumeric.countReduce bits fuel half total=AxlerTheta.countReduce bits fuel half total := by
 induction fuel generalizing half total with
 | zero => rfl
 | succ fuel ih => simp only [DusartNumeric.countReduce,AxlerTheta.countReduce,force_apply,RosserScan.forceNat_eq,combine_eq,ih]
lemma fast_eq (depth mask : Nat) : DusartNumeric.fastCount depth mask=AxlerTheta.fastCount depth mask := by
 simp only [DusartNumeric.fastCount,AxlerTheta.fastCount,force_apply,RosserScan.forceNat_eq,bytes_eq,reduce_eq,DusartNumeric.periodicMask,RosserBitSieve.periodicMask]
lemma count_eq (depth mask : Nat) : DusartNumeric.bitCount depth mask=AxlerTheta.bitCount depth mask := by
 simpa only [DusartNumeric.bitCount,AxlerTheta.bitCount,force_apply,RosserScan.forceNat_eq] using fast_eq depth mask
lemma log_eq (n : Nat) : DusartNumeric.logUpNum n=AxlerTheta.logUpNum n := by rfl
lemma word_eq (fuel a base cand hints : Nat) : DusartNumeric.word fuel a base cand hints=WordWitness.word fuel a base cand hints := by
 induction fuel generalizing cand hints with
 | zero => rfl
 | succ fuel ih => simp only [DusartNumeric.word,WordWitness.word,force_apply,RosserScan.forceNat_eq,ih]
lemma inner_eq (n a base cand hints : Nat) : DusartNumeric.inner n a base cand hints=PackedWords.inner n a base cand hints := by
 induction n generalizing a base cand hints with
 | zero => rfl
 | succ n ih => simp only [DusartNumeric.inner,PackedWords.inner,force_apply,RosserScan.forceNat_eq,word_eq,ih,DusartNumeric.payload,PackedWords.payload,DusartNumeric.rest,PackedWords.rest]
lemma check_eq (groups a base cand : Nat) (hints : List Nat) :
 DusartNumeric.check groups a base cand hints=PackedWords.check groups a base cand hints := by
 induction groups generalizing a base cand hints with
 | zero => rfl
 | succ n ih =>
   cases hints with
   | nil => rfl
   | cons h hs => simp only [DusartNumeric.check,PackedWords.check,force_apply,RosserScan.forceNat_eq,inner_eq,ih]
lemma mask_eq (ps : List (Nat×Nat)) (a b : Nat) :
 DusartNumeric.mask ps a b=RosserCachedSieve.mask ps a b := by rfl
lemma valid_of_check {len : Nat} {ps : List (Nat×Nat)} (hc : DusartNumeric.validCheck len ps=true) : Literal.Valid len ps := by
 simp only [DusartNumeric.validCheck,List.all_eq_true,decide_eq_true_eq] at hc
 intro dm hm
 exact hc dm hm
lemma v8192 : Literal.Valid 8192 DusartNumeric.Base8192.table := valid_of_check DusartNumeric.Base8192.valid
lemma v16384 : Literal.Valid 16384 DusartNumeric.Base16384.table := valid_of_check DusartNumeric.Base16384.valid
lemma v32768 : Literal.Valid 32768 DusartNumeric.Base32768.table := valid_of_check DusartNumeric.Base32768.valid
lemma v65536 : Literal.Valid 65536 DusartNumeric.Base65536.table := valid_of_check DusartNumeric.Base65536.valid
lemma from_cert {groups len depth a u v : Nat} {table : List (Nat×Nat)} {dat : Nat×List Nat}
 (hv : Literal.Valid len table) (hlen : 0<len) (ha : 131073≤a) (htop : a+len<2^64)
 (hgroups : len≤2048*groups) (hdepth : len≤2^(depth+3))
 (hc : DusartNumeric.one groups len depth a u v table dat=true) : Literal.Spec a (a+len) u v := by
 simp only [DusartNumeric.one,Bool.and_eq_true,decide_eq_true_eq] at hc
 have heq := Literal.eq_pairs hv
 have hd : ∀d∈table.map Prod.fst,2≤d := by
   intro d hd
   obtain ⟨dm,hm,rfl⟩ := List.mem_map.mp hd
   exact (hv dm hm).1
 have hb : ∀p, Nat.Prime p → a<p → p≤a+len →
   (RosserCachedSieve.mask table a (a+len)).testBit (p-(a+1))=true := by
   intro p hp hpa hpb
   rw [heq]
   exact RosserCachedSieve.mask_prime len a (a+len) (table.map Prod.fst) hd (by omega) (by omega) p hp hpa hpb
 have hc' : PackedWords.check groups a (RosserCachedSieve.mask table a (a+len)) dat.1 dat.2=true := by
   simpa only [check_eq,mask_eq] using hc.1
 have hcover := PackedWords.interval_cover groups a (a+len) (RosserCachedSieve.mask table a (a+len)) dat.1 dat.2
   ha (by omega) hc' hb
 have ht := WordWitness.theta_upper a (a+len) depth dat.1 (by omega) (by omega) htop
   (by simpa only [Nat.add_sub_cancel_left] using hc.2.1) (by omega) hcover
 have he : u+AxlerTheta.bitCount depth dat.1*AxlerTheta.logUpNum (a+len)=v := by
   simpa only [count_eq,log_eq] using hc.2.2.1
 intro hu
 have hv' : (1000000 : ℝ)*Chebyshev.theta ((a+len : Nat) : ℝ)≤v := by
   have he' : (u : ℝ)+(AxlerTheta.bitCount depth dat.1 : ℝ)*(AxlerTheta.logUpNum (a+len) : ℝ)=(v : ℝ) := by exact_mod_cast he
   push_cast at ht ⊢
   linarith only [hu,ht,he']
 refine ⟨hv',?_⟩
 intro x hx hX
 have hm := Chebyshev.theta_mono hX.le
 have hm' := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ)≤1000000)
 have he' : (10000 : ℝ)*(v : ℝ)≤1000000*(10001*(a : ℝ)+1000000000) := by exact_mod_cast hc.2.2.2
 linarith only [hm',hv',he',hx]
end DusartNumericBridge
namespace DusartNumericBridge
lemma generic_to_theta {a b u v : Nat} (h : DusartNumeric.GenericSpec a b u v) :
 DusartMeshUpper.Literal.Spec a b u v := by
 apply h DusartMeshUpper.Literal.Spec _ @DusartMeshUpper.Literal.compose
 intro groups len depth a u v table dat hv hlen ha htop hgroups hdepth hc
 exact from_cert (valid_of_check hv) hlen ha htop hgroups hdepth hc
end DusartNumericBridge


