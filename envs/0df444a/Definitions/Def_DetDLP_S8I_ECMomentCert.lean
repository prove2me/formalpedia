-- Prove2me | Definitions.Def_DetDLP_S8I_ECMomentCert
-- name    : DetDLP_S8I_ECMomentCert
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:48:41.751227+00:00
-- url     : https://prove2.me/theorems/19f9af53-b1fc-4d4e-8b55-9c649adc5129
-- title:
--   Arithmetic certificates for elliptic-curve pair and moment queries
-- statement:
--   Projection erases the uniquely determined point checks, coordinate conversions, and short-Weierstrass addition transcripts, giving bijections with the corresponding finite semantic witness types.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8I_ECQueryCount
import Definitions.Def_DetDLP_S8C_FpQueryCount
import Definitions.Def_DetDLP_S8K_ECAddArithmetic

set_option autoImplicit false
noncomputable section
namespace DetDLP.S8I.ECMomentCert
open ECQueryCount S8H.ECPointArithmetic S8K S8K.ECAddArithmetic M89S1
variable {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)}

abbrev Checked (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (T : ℕ) :=
  {v : (Fin m → E.toAffine.Point) × (Fin m → Fin 7 → Run p) //
    ∀ i, elemRuns S i (bitLen p) T [] (v.1 i) (v.2 i)}

def atomsEquiv (mul : w3_modMulInterface) (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (T : ℕ) :
    Checked E S T ≃ Tuple (ecFactorBlock E T S) := by
  refine S8C.certEquiv (Fintype.piFinset (ecFactorBlock E T S))
    (fun A (r : Fin m → Fin 7 → Run p) => ∀ i, elemRuns S i (bitLen p) T [] (A i) (r i)) ?_ ?_
  · intro A r h; apply Fintype.mem_piFinset.mpr; intro i
    have hi := h i
    have hu := runs_unique mul E (coords (A i)).2.1 (coords (A i)).2.2 (alpha S i (coords (A i)).2.2) (beta S i (coords (A i)).2.2)
    have hp := (elemRuns_iff mul S i (bitLen p) T [] (A i)).mp ⟨r i,hi,fun _ hs => hu.unique hs.1 hi.1⟩
    simpa [S8H.ECPointGadget.elemPin,ecFactorBlock] using hp
  · intro A h
    have H (i : Fin m) := Fintype.mem_piFinset.mp h i
    have ex (i : Fin m) := (elemRuns_iff mul S i (bitLen p) T [] (A i)).mpr (by
      simpa [S8H.ECPointGadget.elemPin,ecFactorBlock] using H i)
    choose r hr ur using ex
    exact ⟨r,hr,fun s hs => funext fun i => ur i _ (hs i)⟩

/-- A leaf converts one original point; a branch checks one short-model addition. -/
inductive Tree (A : Type) where | leaf : A → Tree A | add : Tree A → Tree A → Tree A
namespace Tree
variable {A : Type}
def chain : (n : ℕ) → (Fin (n+1) → A) → Tree A
  | 0, a => .leaf (a 0)
  | n+1, a => .add (.leaf (a 0)) (chain n (fun i => a i.succ))
def value [Add A] : Tree A → A | .leaf a => a | .add l r => l.value + r.value
theorem chain_value [AddCommMonoid A] (n : ℕ) (a : Fin (n+1) → A) : (chain n a).value = ∑ i, a i := by
  induction n with
  | zero => simp [chain,value]
  | succ n ih => rw [Fin.sum_univ_succ]; simp only [chain,value,ih]

def maps : Tree A → ℕ | .leaf _ => 1 | .add l r => l.maps + r.maps
def adds : Tree A → ℕ | .leaf _ => 0 | .add l r => l.adds + r.adds + 1
theorem chain_size (n : ℕ) (a : Fin (n+1) → A) : (chain n a).maps = n+1 ∧ (chain n a).adds = n := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    obtain ⟨hm,ha⟩ := ih (fun i => a i.succ)
    simp only [chain,maps,adds,hm,ha]; omega

def Transcript (p : ℕ) : Tree A → Type
  | .leaf _ => Coords p × MapCert p
  | .add l r => Transcript p l × Transcript p r × Coords p × AddCert p
def out : (t : Tree A) → Transcript p t → Coords p
  | .leaf _, c => c.1 | .add _ _, c => c.2.2.1
def ok : (t : Tree E.toAffine.Point) → Transcript p t → Prop
  | .leaf a, c => ecToSWOK E (coords a) c.1 c.2
  | .add l r, c => ok l c.1 ∧ ok r c.2.1 ∧ swAddOK E (out l c.1) (out r c.2.1) c.2.2.1 c.2.2.2
abbrev Valid (t : Tree E.toAffine.Point) := {c : Transcript p t // ok t c}
variable [E.IsElliptic] (hp : 3 < p) (mul : w3_modMulInterface)
abbrev sw := SWEquiv.equiv E (SWEquiv.six_ne_zero hp)
include mul in
theorem sound (t : Tree E.toAffine.Point) (c : Valid t) : out t c.val = swCoords (sw hp t.value) := by
  induction t with
  | leaf a => exact ecToSW_sound E hp mul a _ _ c.2
  | add l r il ir =>
    have h := c.2.2.2
    rw [il ⟨_,c.2.1⟩, ir ⟨_,c.2.2.1⟩] at h
    simpa only [out,value,map_add] using swAdd_sound E mul _ _ _ _ h

include hp mul in
theorem unique (t : Tree E.toAffine.Point) : Nonempty (Unique (Valid t)) := by
  induction t with
  | leaf a =>
    obtain ⟨k,hk,uk⟩ := ecToSW_unique E hp mul a
    refine ⟨⟨⟨⟨(_,k),hk⟩⟩,?_⟩⟩
    rintro ⟨⟨v,s⟩,hs⟩; obtain rfl := ecToSW_sound E hp mul a v s hs
    exact Subtype.ext (Prod.ext rfl (uk s hs))
  | add l r il ir =>
    obtain ⟨⟨u,hu⟩⟩ := il; obtain ⟨⟨v,hv⟩⟩ := ir
    obtain ⟨s,hs,us⟩ := swAdd_unique E mul (sw hp l.value) (sw hp r.value)
    have H := hs
    rw [← sound hp mul l u.default, ← sound hp mul r v.default] at H
    refine ⟨⟨⟨⟨(u.default.val,v.default.val,_,s),u.default.2,v.default.2,H⟩⟩,?_⟩⟩
    rintro ⟨⟨a,b,o,k⟩,ha,hb,hk⟩
    obtain rfl : a = u.default.val := congrArg Subtype.val (hu ⟨a,ha⟩)
    obtain rfl : b = v.default.val := congrArg Subtype.val (hv ⟨b,hb⟩)
    rw [sound hp mul l u.default,sound hp mul r v.default] at hk
    obtain rfl := swAdd_sound E mul _ _ o k hk
    exact Subtype.ext (congrArg (fun q => (_,_,_,q)) (us k hk))
end Tree

private theorem coords_inj {F : WeierstrassCurve (ZMod p)} : Function.Injective (@coords p _ F) := by
  intro x y h; cases x <;> cases y <;> simp_all [coords]

private def erase {A B : Type} {C : A → Type} (e : A ≃ B) (u : ∀ a, Nonempty (Unique (C a))) :
    (Σ a, C a) ≃ B where
  toFun v := e v.1
  invFun b := ⟨e.symm b,(u _).some.default⟩
  left_inv := by
    rintro ⟨a,c⟩
    exact (congrArg (fun x => Sigma.mk x (u x).some.default) (e.symm_apply_apply a)).trans
      (congrArg (Sigma.mk a) ((u a).some.uniq c).symm)
  right_inv b := e.apply_symm_apply b

abbrev SeedCert (p m : ℕ) (η : List Bool) := {v : ECSeed p m × (Fin (m*4*bitLen p) → Bool) //
  v.2 = ecBits v.1 ∧ (List.ofFn v.2).take η.length = η}
def massEquiv (p m : ℕ) (η : List Bool) : SeedCert p m η ≃ Mass p m η := by
  refine S8C.certEquiv (seedSet p m η) (fun S w => w = ecBits S ∧ (List.ofFn w).take η.length = η) ?_ ?_
  · rintro S _ ⟨rfl,h⟩; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  · intro S h; exact ⟨ecBits S,⟨rfl,(Finset.mem_filter.mp h).2⟩,fun _ hw => hw.1⟩

variable (E) (T : ℕ) (η : List Bool)
abbrev SingleCert := Σ s : SeedCert p m η, Checked E s.val.1 T
abbrev DoubleCert := Σ s : SeedCert p m η, Checked E s.val.1 T × Checked E s.val.1 T
def singleEquiv (mul : w3_modMulInterface) : SingleCert (m := m) E T η ≃ Single p m E T η :=
  Equiv.sigmaCongr (massEquiv p m η) (fun s => atomsEquiv mul E s.val.1 T)
def doubleEquiv (mul : w3_modMulInterface) : DoubleCert (m := m) E T η ≃ Double p m E T η :=
  Equiv.sigmaCongr (massEquiv p m η) (fun s => (atomsEquiv mul E s.val.1 T).prodCongr (atomsEquiv mul E s.val.1 T))

variable (S : ECSeed p (m+1))
abbrev SumRun := Σ a : Checked E S T, (Tree.chain m a.val.1).Valid
abbrev sumOut (v : SumRun E T S) := (Tree.chain m v.1.val.1).out v.2.val
abbrev Joined := {v : SumRun E T S × SumRun E T S // sumOut E T S v.1 = sumOut E T S v.2}
abbrev EqualSumCert := Σ s : SeedCert p (m+1) η, Joined E T s.val.1
variable [E.IsElliptic] (hp : 3 < p) (mul : w3_modMulInterface)
def joinedEquiv : Joined E T S ≃ Collision (ecFactorBlock E T S) := by
  let e : SumRun E T S ≃ Tuple (ecFactorBlock E T S) := erase (atomsEquiv mul E S T) (fun a => Tree.unique hp mul (Tree.chain m a.val.1))
  have H (v : SumRun E T S) : sumOut E T S v = swCoords (Tree.sw hp (∑ i, (e v).val i)) := by
    exact (Tree.sound hp mul _ v.2).trans (congrArg (fun x => swCoords (Tree.sw hp x)) (Tree.chain_value m v.1.val.1))
  refine Equiv.subtypeEquiv (e.prodCongr e) (fun v => ?_)
  rw [H,H]; exact (coords_inj.eq_iff).trans (Tree.sw hp).injective.eq_iff

def equalSumEquiv : EqualSumCert (m := m) E T η ≃ EqualSum p (m+1) E T η :=
  Equiv.sigmaCongr (massEquiv p (m+1) η) (fun s => joinedEquiv E T s.val.1 hp mul)

abbrev pairTree (ab : Checked E S T × Checked E S T) :=
  (Tree.chain m ab.1.val.1).add (Tree.chain m ab.2.val.1)
omit [E.IsElliptic] in
theorem pairTree_size (ab : Checked E S T × Checked E S T) : (pairTree E T S ab).maps = 2*(m+1) ∧
    (pairTree E T S ab).adds = 2*(m+1)-1 := by
  simp only [Tree.maps,Tree.adds,(Tree.chain_size m _).1,(Tree.chain_size m _).2]; omega

abbrev PairRun := Σ ab : Checked E S T × Checked E S T, (pairTree E T S ab).Valid
abbrev PairCert (b : ℕ) (X : E.toAffine.Point) := {v : PairRun E T S //
  (tupleWord (ecWord b) (v.1.1.val.1,v.1.2.val.1)).take η.length = η ∧
  (pairTree E T S v.1).out v.2.val = swCoords (Tree.sw hp X)}

def pairEquiv (b : ℕ) (X : E.toAffine.Point) : PairCert E T η S hp b X ≃ PairSet p (m+1) E T η b S X := by
  let D := ecFactorBlock E T S
  let e := atomsEquiv mul E S T
  let f : PairRun E T S ≃ Tuple D × Tuple D := erase (e.prodCongr e) (fun ab => Tree.unique hp mul (pairTree E T S ab))
  let pred (ab : Tuple D × Tuple D) := (tupleWord (ecWord b) (ab.1.val,ab.2.val)).take η.length = η ∧
    (∑ i, (ab.1.val i + ab.2.val i)) = X
  have H (v : PairRun E T S) : (pairTree E T S v.1).value = ∑ i, ((f v).1.val i + (f v).2.val i) := by
    rw [Finset.sum_add_distrib]; exact congrArg₂ (· + ·) (Tree.chain_value m _) (Tree.chain_value m _)
  refine (Equiv.subtypeEquiv (p := _) (q := pred) f (fun v => ?_)).trans ?_
  · change (_ ∧ (pairTree E T S v.1).out v.2.val = _) ↔ (_ ∧ _)
    rw [Tree.sound hp mul _ v.2,H]; exact and_congr_right fun _ => (coords_inj.eq_iff).trans (Tree.sw hp).injective.eq_iff
  · have mem (ab : PointPair p (m+1) E) : ab ∈ pairSet p (m+1) E T η b S X ↔
        (∀ i, ab.1 i ∈ D i ∧ ab.2 i ∈ D i) ∧ (tupleWord (ecWord b) ab).take η.length = η ∧
        (∑ i, (ab.1 i + ab.2 i)) = X := by simp [pairSet,D]
    exact { toFun := fun v => ⟨(v.1.1.val,v.1.2.val),(mem _).mpr ⟨fun i =>
              ⟨Fintype.mem_piFinset.mp v.1.1.2 i,Fintype.mem_piFinset.mp v.1.2.2 i⟩,v.2⟩⟩
            invFun := fun v => ⟨(⟨v.val.1,Fintype.mem_piFinset.mpr fun i => ((mem _).mp v.2).1 i |>.1⟩,
              ⟨v.val.2,Fintype.mem_piFinset.mpr fun i => ((mem _).mp v.2).1 i |>.2⟩),((mem _).mp v.2).2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }

end DetDLP.S8I.ECMomentCert


