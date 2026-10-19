-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
-- name    : OAI_Combinatorics_HoneycombCorridor_Contours
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:28:38.205169+00:00
-- url     : https://prove2.me/theorems/db5897a6-66fd-42f4-98dd-7f3f22de4134
-- title:
--   Oriented flows, face sides of germs and contours of simple loops
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Oriented flow.** The oriented flow of an edge chain assigns to each germ $(v,k)$ the signed amount flowing out of $v$ along slot $k$. For a word flow it equals the turn-visit chain plus the boundary terms at the start and end.
--   2. **Faces of a germ.** Each germ has a left face and a right face (the right face of $g$ is the left face of $\mathrm{reverseGerm}(g)$). A face potential $p$ represents an edge chain $q$ if the oriented flow at every germ equals $p(\mathrm{left})-p(\mathrm{right})$; every closed word flow has a representing potential.
--   3. **Contours.** A chain is a local contour at $(g,b)$ if at $g$'s vertex its oriented flow is $+1$ on the outgoing slot, $-1$ on the incoming slot and $0$ on the third. It is a word contour along $w$ if this holds at every step. Simple closed walks give word contours, and along a contour the potential is constant on each side, with jump $p(\mathrm{right})-p(\mathrm{left})=1$.
--   4. **Indicator potentials.** For a nonempty simple closed walk, the representing potential is nonzero and takes only the values $0$ and $\varepsilon\in\{1,-1\}$: it is $\pm$ the indicator of the faces enclosed by the loop.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Contours.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Contours.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def orientedFlow : (EdgeIndex →₀ ℤ) →+ (Germ →₀ ℤ) :=
  Finsupp.liftAddHom fun e =>
    Finsupp.singleAddHom (upEnd e,e.2) - Finsupp.singleAddHom (downEnd e,e.2)

@[simp] theorem orientedFlow_single (e : EdgeIndex) (a : ℤ) :
    orientedFlow (Finsupp.single e a) =
      Finsupp.single (upEnd e,e.2) a - Finsupp.single (downEnd e,e.2) a := by
  simp [orientedFlow]

@[simp] theorem orientedFlow_dartFlow (g : Germ) :
    orientedFlow (dartFlow g) = Finsupp.single g 1 - Finsupp.single (reverseGerm g) 1 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [dartFlow,edgeOf,dartSign,upEnd,downEnd,neighbor,reverseGerm]

noncomputable def turnVisit : Germ → List Bool → (Germ →₀ ℤ)
  | _, [] => 0
  | g, b :: w =>
      Finsupp.single (g.1,outgoingSlot g b) 1 - Finsupp.single g 1 +
        turnVisit (advance g b) w

theorem orientedFlow_wordFlow (g : Germ) (w : List Bool) :
    orientedFlow (wordFlow g w) =
      turnVisit g w + Finsupp.single g 1 - Finsupp.single (terminalGerm g w) 1 := by
  induction w generalizing g with
  | nil => simp [wordFlow,turnVisit,terminalGerm]
  | cons b w ih =>
      simp only [wordFlow,map_add,orientedFlow_dartFlow,turnVisit,terminalGerm,ih]
      have h : reverseGerm (g.1,outgoingSlot g b) = advance g b := rfl
      rw [h]
      abel

theorem turnVisit_eq_zero_of_not_mem (g : Germ) (w : List Bool) (v : Vertex)
    (k : Fin 3) (hv : v ∉ traced g w) : turnVisit g w (v,k) = 0 := by
  classical
  induction w generalizing g with
  | nil => simp [turnVisit]
  | cons b w ih =>
      simp only [traced,List.mem_cons,not_or] at hv
      have hne : (v,k) ≠ g := by intro h; exact hv.1 (congrArg Prod.fst h)
      have hne' : (g.1,outgoingSlot g b) ≠ (v,k) := by
        intro h; exact hv.1 (congrArg Prod.fst h).symm
      simp [turnVisit,ih _ hv.2,hne,hne']

theorem simple_closed_word_local (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup) (hc : terminalGerm g (b :: w) = g)
    (k : Fin 3) :
    orientedFlow (wordFlow g (b :: w)) (g.1,k) =
      (if k = outgoingSlot g b then 1 else 0) - (if k = g.2 then 1 else 0) := by
  classical
  rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
  simp only [traced,List.nodup_cons] at hN
  have ht := turnVisit_eq_zero_of_not_mem (advance g b) w g.1 k hN.1
  rcases g with ⟨v,j⟩
  simp [turnVisit,ht,Finsupp.single_apply,eq_comm]

theorem orientedFlow_up (q : EdgeIndex →₀ ℤ) (i j : ℤ) (k : Fin 3) :
    orientedFlow q (.up i j,k) = q ((i,j),k) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]
  | single e a =>
      rcases e with ⟨⟨x,y⟩,l⟩
      fin_cases l <;> fin_cases k <;>
        simp [orientedFlow_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem orientedFlow_down (q : EdgeIndex →₀ ℤ) (i j : ℤ) (k : Fin 3) :
    orientedFlow q (.down i j,k) = -q (edgeOf (.down i j,k)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,l⟩
      have hy : j = y - 1 ↔ y = j + 1 := by omega
      have hx : i = x - 1 ↔ x = i + 1 := by omega
      fin_cases l <;> fin_cases k <;>
        simp [orientedFlow_single,edgeOf,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

def leftFace : Germ → FaceIndex
  | (.up i j,k) => if k = 0 then (i,j) else if k = 1 then (i-1,j+1) else (i-1,j)
  | (.down i j,k) => if k = 0 then (i-1,j+1) else if k = 1 then (i,j) else (i,j+1)

def rightFace (g : Germ) : FaceIndex := leftFace (reverseGerm g)

def RepresentsFlow (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ) : Prop :=
  ∀ g : Germ, orientedFlow q g = p (leftFace g) - p (rightFace g)

theorem closed_word_has_potential (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) :
    ∃ p : FaceIndex →₀ ℤ, RepresentsFlow p (wordFlow g w) := by
  obtain ⟨p,hp⟩ := closed_word_has_finite_potential g w hc
  refine ⟨p, ?_⟩
  intro d
  rcases d with ⟨v,k⟩
  cases v with
  | up i j =>
      have h := hp i j
      fin_cases k <;>
        simp [orientedFlow_up,leftFace,rightFace,reverseGerm,neighbor] <;> omega
  | down i j =>
      have h0 := (hp i (j+1)).1
      have h1 := (hp i j).2.1
      have h2 := (hp (i+1) j).2.2
      fin_cases k <;>
        simp [orientedFlow_down,edgeOf,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

@[simp] theorem wordFlow_append (g : Germ) (u w : List Bool) :
    wordFlow g (u ++ w) = wordFlow g u + wordFlow (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => simp [wordFlow,terminalGerm]
  | cons b u ih => simp [wordFlow,terminalGerm,ih,add_assoc]

theorem closed_word_rotate (g : Germ) (u w : List Bool)
    (hN : (traced g (u ++ w)).Nodup) (hc : terminalGerm g (u ++ w) = g) :
    let g' := terminalGerm g u
    (traced g' (w ++ u)).Nodup ∧
    terminalGerm g' (w ++ u) = g' ∧ wordFlow g' (w ++ u) = wordFlow g (u ++ w) := by
  dsimp only
  have ht : terminalGerm (terminalGerm g u) w = g := by simpa using hc
  rw [traced_append] at hN
  simp only [traced_append,terminalGerm_append,wordFlow_append,ht]
  exact ⟨List.nodup_append_comm.mp hN,trivial,add_comm _ _⟩

def LocalContour (q : EdgeIndex →₀ ℤ) (g : Germ) (b : Bool) : Prop :=
  ∀ k : Fin 3, orientedFlow q (g.1,k) =
    (if k = outgoingSlot g b then 1 else 0) - (if k = g.2 then 1 else 0)

def WordContour (q : EdgeIndex →₀ ℤ) : Germ → List Bool → Prop
  | _, [] => True
  | g, b :: w => LocalContour q g b ∧ WordContour q (advance g b) w

theorem wordContour_of_splits (q : EdgeIndex →₀ ℤ) (g : Germ) (w : List Bool)
    (hs : ∀ u b v, w = u ++ b :: v → LocalContour q (terminalGerm g u) b) :
    WordContour q g w := by
  induction w generalizing g with
  | nil => trivial
  | cons b w ih =>
      refine ⟨by simpa only [terminalGerm] using hs [] b w rfl, ih (advance g b) ?_⟩
      intro u c v hv
      simpa only [terminalGerm] using hs (b :: u) c v (by simp [hv])

theorem simple_closed_word_contour (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    WordContour (wordFlow g w) g w := by
  apply wordContour_of_splits
  intro u b v h
  subst w
  obtain ⟨hN',hc',hq⟩ := closed_word_rotate g u (b :: v) hN hc
  rw [← hq]
  intro k
  exact simple_closed_word_local (terminalGerm g u) b (v ++ u) hN' hc' k

theorem localContour_sides (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (b : Bool) (hl : LocalContour q g b) :
    p (rightFace (advance g b)) = p (rightFace g) ∧
    p (leftFace (advance g b)) = p (leftFace g) ∧
    p (rightFace g) - p (leftFace g) = 1 := by
  have h0 := (hp (g.1,0)).symm.trans (hl 0)
  have h1 := (hp (g.1,1)).symm.trans (hl 1)
  have h2 := (hp (g.1,2)).symm.trans (hl 2)
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    simp [advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

@[simp] theorem rightFace_reverse (g : Germ) :
    rightFace (reverseGerm g) = leftFace g := by simp [rightFace]

@[simp] theorem reverseGerm_advance (g : Germ) (b : Bool) :
    reverseGerm (advance g b) = (g.1,outgoingSlot g b) := by
  simp [reverseGerm,advance]

def canonicalDart (e : EdgeIndex) : Germ := (upEnd e,e.2)

theorem canonicalDart_edgeOf (g : Germ) :
    canonicalDart (edgeOf g) = g ∨ canonicalDart (edgeOf g) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [canonicalDart,edgeOf,upEnd,reverseGerm,neighbor]

def SideValues (p : FaceIndex →₀ ℤ) (L R : ℤ) (g : Germ) : Prop :=
  (p (leftFace g) = L ∨ p (leftFace g) = R) ∧
    (p (rightFace g) = L ∨ p (rightFace g) = R)

theorem SideValues.reverse {p : FaceIndex →₀ ℤ} {L R : ℤ} {g : Germ}
    (h : SideValues p L R g) : SideValues p L R (reverseGerm g) := by
  exact ⟨h.2,by simpa only [rightFace_reverse] using h.1⟩

theorem SideValues.canonical {p : FaceIndex →₀ ℤ} {L R : ℤ} {g : Germ}
    (h : SideValues p L R g) : SideValues p L R (canonicalDart (edgeOf g)) := by
  rcases canonicalDart_edgeOf g with he | he
  · exact he ▸ h
  · exact he ▸ h.reverse

theorem wordFlow_edge_sides (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (w : List Bool) (hw : WordContour q g w)
    (e : EdgeIndex) (he : wordFlow g w e ≠ 0) :
    SideValues p (p (rightFace g)) (p (leftFace g)) (canonicalDart e) := by
  classical
  induction w generalizing g with
  | nil => simp [wordFlow] at he
  | cons b w ih =>
      obtain ⟨hr,hl,_⟩ := localContour_sides p q hp g b hw.1
      by_cases hz : dartFlow (g.1,outgoingSlot g b) e = 0
      · have ht : wordFlow (advance g b) w e ≠ 0 := by
          simpa only [wordFlow,Finsupp.add_apply,hz,zero_add] using he
        have hs := ih (advance g b) hw.2 ht
        rw [hr,hl] at hs
        exact hs
      · have heq : edgeOf (g.1,outgoingSlot g b) = e := by
          by_contra h
          exact hz (by simp [dartFlow,h])
        have hs : SideValues p (p (rightFace g)) (p (leftFace g)) (advance g b) :=
          ⟨Or.inr hl,Or.inl hr⟩
        have hs' := hs.reverse.canonical
        simpa only [reverseGerm_advance,heq] using hs'

theorem RepresentsFlow.horizontal {p : FaceIndex →₀ ℤ} {q : EdgeIndex →₀ ℤ}
    (hp : RepresentsFlow p q) (i j : ℤ) :
    q ((i,j),0) = p (i,j) - p (i-1,j) := by
  simpa [orientedFlow_up,leftFace,rightFace,reverseGerm,neighbor] using hp (.up i j,0)

theorem finite_potential_has_zero_side (p : FaceIndex →₀ ℤ) (hp : p ≠ 0) :
    ∃ i j : ℤ, p (i,j) ≠ 0 ∧ p (i-1,j) = 0 := by
  classical
  let S : Finset ℤ := p.support.image Prod.fst
  have hS : S.Nonempty := (Finsupp.support_nonempty_iff.mpr hp).image Prod.fst
  obtain ⟨a,ha,hmin⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
  refine ⟨a.1,a.2,Finsupp.mem_support_iff.mp ha,?_⟩
  by_contra hne
  have hm : a.1 - 1 ∈ S := Finset.mem_image.mpr
    ⟨(a.1-1,a.2),Finsupp.mem_support_iff.mpr hne,rfl⟩
  have h := Finset.min'_le S (a.1-1) hm
  omega

theorem finite_potential_two_values (p : FaceIndex →₀ ℤ) (L R : ℤ) (hp : p ≠ 0)
    (hgrad : ∀ i j : ℤ, p (i,j) - p (i-1,j) ≠ 0 →
      (p (i,j) = L ∨ p (i,j) = R) ∧ (p (i-1,j) = L ∨ p (i-1,j) = R)) :
    (L = 0 ∨ R = 0) ∧ ∀ a : FaceIndex, p a = L ∨ p a = R := by
  obtain ⟨i,j,hne,hzero⟩ := finite_potential_has_zero_side p hp
  have hz : L = 0 ∨ R = 0 := by
    have h := (hgrad i j (by simpa [hzero] using hne)).2
    rw [hzero] at h
    exact h.imp Eq.symm Eq.symm
  refine ⟨hz,?_⟩
  rintro ⟨i,j⟩
  let m : ℤ := -(faceRadius p : ℤ) - 1
  have hleft (k : ℤ) (hk : k ≤ m) : p (k,j) = 0 := by
    by_contra hne
    have hb := (mem_support_in_box p (k,j) (Finsupp.mem_support_iff.mpr hne)).1
    dsimp [m] at hk
    omega
  have hbase : p (m,j) = L ∨ p (m,j) = R := by
    rw [hleft m le_rfl]
    exact hz.imp Eq.symm Eq.symm
  by_cases him : i ≤ m
  · rw [hleft i him]
    exact hz.imp Eq.symm Eq.symm
  · have hmi : m ≤ i := by omega
    apply Int.leInduction (motive := fun k _ => p (k,j) = L ∨ p (k,j) = R) hbase ?_ i hmi
    intro k _ hk
    by_cases hg : p (k+1,j) - p (k,j) = 0
    · have heq : p (k+1,j) = p (k,j) := by omega
      exact heq ▸ hk
    · simpa only [add_sub_cancel_right] using (hgrad (k+1) j (by simpa using hg)).1

theorem simple_closed_word_indicator (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    ∃ (p : FaceIndex →₀ ℤ) (ε : ℤ), RepresentsFlow p (wordFlow g w) ∧ p ≠ 0 ∧
      (ε = 1 ∨ ε = -1) ∧ ∀ a : FaceIndex, p a = 0 ∨ p a = ε := by
  obtain ⟨p,hp⟩ := closed_word_has_potential g w hc
  have hw := simple_closed_word_contour g w hN hc
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hne
  have hs := localContour_sides p (wordFlow g (b :: u)) hp g b hw.1
  let L := p (rightFace g)
  let R := p (leftFace g)
  have hLR : L - R = 1 := hs.2.2
  have hpne : p ≠ 0 := by
    intro hz
    simp only [L,R,hz,Finsupp.zero_apply,sub_zero] at hLR
    omega
  have ht : (L = 0 ∨ R = 0) ∧ ∀ a : FaceIndex, p a = L ∨ p a = R := by
    apply finite_potential_two_values p L R hpne
    intro i j hij
    have hq : wordFlow g (b :: u) ((i,j),0) ≠ 0 := by
      simpa only [hp.horizontal i j] using hij
    have h := wordFlow_edge_sides p _ hp g (b :: u) hw ((i,j),0) hq
    simpa [SideValues,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor,L,R] using h
  rcases ht.1 with hL | hR
  · have hRm : R = -1 := by omega
    refine ⟨p,-1,hp,hpne,Or.inr rfl,?_⟩
    intro a
    simpa only [hL,hRm] using ht.2 a
  · have hLp : L = 1 := by omega
    refine ⟨p,1,hp,hpne,Or.inl rfl,?_⟩
    intro a
    simpa only [hLp,hR,or_comm] using ht.2 a

end PolynomialVacuumBridge.Corridor

end

end OAI


