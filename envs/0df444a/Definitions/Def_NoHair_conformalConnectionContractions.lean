-- Prove2me | Definitions.Def_NoHair_conformalConnectionContractions
-- name    : NoHair_conformalConnectionContractions
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T10:26:42.375147+00:00
-- url     : https://prove2.me/theorems/6e78672a-c79e-47fd-9e94-9c7c82f133db
-- title:
--   Algebraic contractions of the conformal change of connection
-- statement:
--   The difference of the Levi-Civita connections of conformally related metrics is a tensor of the form $\delta^a_i p_j+\delta^a_jp_i-h_{ij}q^a$. The coordinate contractions give its trace and the mixed and quadratic terms in the change of the Ricci tensor.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

noncomputable section

namespace NoHair.ConformalConnection

abbrev I := Fin 3
abbrev Mat := Matrix I I ℝ

def kr (a i : I) : ℝ := if a=i then 1 else 0

abbrev Symb := I → I → I → ℝ

def connectionChange (m : Mat) (p q : I → ℝ) (a i j : I) : ℝ :=
  kr a i*p j + kr a j*p i - m i j*q a

def quadratic (G : Symb) (i j : I) : ℝ :=
  ∑ a : I, ∑ l : I, (G a a l*G l j i - G a j l*G l a i)

def mixed (G C : Symb) (i j : I) : ℝ :=
  ∑ a : I, ∑ l : I, (G a a l*C l j i + C a a l*G l j i -
    G a j l*C l a i - C a j l*G l a i)

lemma deltaSum (i : I) (f : I → ℝ) : (∑ a : I, kr a i*f a)=f i := by
  simp [kr,ite_mul]

lemma contract_upper_index (m : Mat) (p q v : I → ℝ) (i j : I) :
    (∑ a : I, v a * connectionChange m p q a i j) =
      v i*p j + v j*p i - m i j*(∑ a : I, v a*q a) := calc
  _ = (∑ a : I, kr a i*v a)*p j + (∑ a : I, kr a j*v a)*p i - m i j*(∑ a : I, v a*q a) := by
    simp only [Fin.sum_univ_three,connectionChange]; ring
  _ = _ := by rw [deltaSum i v,deltaSum j v]

lemma trace_change (m : Mat) (p q : I → ℝ) (hm : ∀ a b, m a b=m b a)
    (lo : ∀ a, p a=∑ l : I, m a l*q l) (i : I) : (∑ a : I, connectionChange m p q a a i)=3*p i := calc
  _ = (∑ _a : I, p i) + (∑ a : I, kr a i*p a) - (∑ a : I, m i a*q a) := by
    simp only [connectionChange,show ∀ a : I, kr a a = 1 by simp [kr],one_mul,hm _ i,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  _ = _ := by rw [deltaSum i p,←lo]; simp [Fin.sum_univ_three] <;> ring

set_option maxHeartbeats 450000 in
lemma mixed_contraction (m : Mat) (G : Symb) (p q : I → ℝ)
    (hm : ∀ a b, m a b=m b a) (hG : ∀ a b c, G a b c=G a c b)
    (lo : ∀ a, p a=∑ l : I, m a l*q l) (i j : I) :
    mixed G (connectionChange m p q) i j =
    (∑ a : I, ((∑ l : I, m j l*G l a i) + ∑ l : I, m l i*G l a j)*q a) +
    (∑ l : I, G l j i*p l) - m j i*(∑ a : I, ∑ l : I, G a a l*q l) := by
  let C := connectionChange m p q
  have form : mixed G C i j =
      (∑ a : I, ∑ l : I, G a a l*C l j i) + (∑ l : I, (∑ a : I, C a a l)*G l j i) -
      (∑ a : I, ∑ l : I, G a j l*C l a i) - (∑ l : I, ∑ a : I, G l a i*C a j l) := by
    have t2 : (∑ a : I, ∑ l : I, C a a l*G l j i) = ∑ l : I, (∑ a : I, C a a l)*G l j i := by
      simp only [Finset.sum_mul]; exact Finset.sum_comm
    have t4 : (∑ a : I, ∑ l : I, C a j l*G l a i) = ∑ l : I, ∑ a : I, G l a i*C a j l := calc
      _ = ∑ l : I, ∑ a : I, C a j l*G l a i := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => mul_comm _ _
    simp only [mixed,Finset.sum_sub_distrib,Finset.sum_add_distrib,t2,t4]
  change mixed G C i j = _
  rw [form]
  have A (a : I) := contract_upper_index m p q (fun l => G a a l) j i
  have B (a : I) := contract_upper_index m p q (fun l => G a j l) a i
  have D (l : I) := contract_upper_index m p q (fun a => G l a i) j l
  dsimp only [C]
  simp only [A,B,D,trace_change m p q hm lo]
  simp only [Fin.sum_univ_three,hm,hG]
  ring

lemma quadratic_contraction (m : Mat) (p q : I → ℝ) (hm : ∀ a b, m a b=m b a)
    (lo : ∀ a, p a=∑ l : I, m a l*q l) (i j : I) :
    quadratic (connectionChange m p q) i j=p i*p j - m j i*(∑ a : I, p a*q a) := by
  let C := connectionChange m p q
  have cs (a r l : I) : C a r l=C a l r := by dsimp only [C,connectionChange]; rw [hm r l]; ring
  have cov (a : I) :
      (∑ l : I, m j l*C l a i) + (∑ l : I, m l i*C l a j) = 2*m j i*p a := by
    have col : (∑ l : I, m l i*C l a j) = ∑ l : I, m i l*C l a j :=
      Finset.sum_congr rfl fun l _ => congrArg (fun v => v*C l a j) (hm l i)
    rw [col]
    dsimp only [C]
    rw [contract_upper_index m p q (m j) a i,contract_upper_index m p q (m i) a j,←lo j,←lo i]
    simp only [hm]; ring
  have sq : mixed C C i j=2*quadratic C i j := by
    simp only [mixed,quadratic,Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => by ring
  have tr : (∑ a : I, ∑ l : I, C a a l*q l) = 3*(∑ l : I, p l*q l) := calc
    _ = ∑ l : I, (∑ a : I, C a a l)*q l := by simp only [Finset.sum_mul]; exact Finset.sum_comm
    _ = _ := by dsimp only [C]; simp only [trace_change m p q hm lo,Fin.sum_univ_three]; ring
  have v : (∑ l : I, C l j i*p l) = p j*p i+p i*p j-m j i*(∑ a : I, p a*q a) := calc
    _ = ∑ l : I, p l*C l j i := Finset.sum_congr rfl fun l _ => mul_comm _ _
    _ = _ := contract_upper_index m p q p j i
  have E := mixed_contraction m C p q hm cs lo i j
  change mixed C C i j = _ at E
  rw [sq] at E
  simp only [cov,tr,v] at E
  simp only [Fin.sum_univ_three] at E
  change quadratic C i j=_
  simp only [Fin.sum_univ_three]
  linear_combination E / 2

lemma quadratic_add (G C : Symb) (i j : I) :
    quadratic (fun a r l => G a r l+C a r l) i j =
    quadratic G i j + mixed G C i j + quadratic C i j := by
  simp only [quadratic,mixed,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => by ring


end NoHair.ConformalConnection


