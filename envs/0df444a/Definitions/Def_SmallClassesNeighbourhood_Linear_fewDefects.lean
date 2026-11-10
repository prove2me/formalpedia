-- Prove2me | Definitions.Def_SmallClassesNeighbourhood_Linear_fewDefects
-- name    : SmallClassesNeighbourhood_Linear_fewDefects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:36:42.509732+00:00
-- url     : https://prove2.me/theorems/9d5dd1b8-2cfb-4873-b798-c44c71519875
-- title:
--   Tagged incidence graph and selections in the few-defects case
-- statement:
--   In the canonical setting let d<C_0^2|A|. Form a graph on disjoint tagged copies of the profile and defect families, with one edge {P_v,D_v} for each good vertex v. Choose subfamilies P_0,D_0 for which the induced graph has minimum degree at least Δ=⌈C^(1/3)⌉ and a spanning tree T of maximum degree at most Δ. T has exactly the tagged vertices of P_0 and D_0; it need not be an induced tree.
--
--   Let B_0 consist of the good vertices with profile in P_0 and defect in D_0. Choose v(P)∈B_0 of profile P and u(D)∈B_0 of defect D. Their image sets are B_0^pro and B_0^def; B_0^tree consists of good vertices whose profile–defect pair is a tree edge. Choose A_0^pro⊆Q and A_0^def⊆A∖Q with sizes at most |P_0|−1 and |D_0|−1, respectively. Each set distinguishes its family by intersection and is itself distinguished by the dual incidence relation. Put Q_0=rep(A_0^def); choose a witness R_0⊆R of size at most |Q_0|−1 that is Q_0-diverse. Define
--
--   $$A'=A_0^{pro}\cup A_0^{def}\cup Q_0,\quad B'=B_0\cup R_0,\quad B''=B_0^{pro}\cup B_0^{def}\cup B_0^{tree}\cup R_0,\quad n'=2(|P_0|+|D_0|).$$
--
--   H_0 is the subgroup of Aut(F[A′,B″]) preserving the seven named sets. The raw assignment sends tagged P to tagged P_{σ(v(P))}, and tagged D to tagged D_{σ(u(D))}. Its landing in Aut(T), multiplication law and stabilizer triviality remain conclusions of Claim 22. The B-sets may overlap; A_0^pro and Q_0 may also overlap.
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), §3.2.3, printed pp. 19–22 (PDF pp. 20–23)

import Definitions.Def_SmallClassesNeighbourhood_Linear_canonical

noncomputable section

namespace SmallClassesNeighbourhood.Linear
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Distinct tags are essential even if a profile and a defect happen to be equal sets. -/
def pdGraph {C0 : ℕ} {F : SimpleGraph V} (s : CanonicalData C0 F) :
    SimpleGraph (Finset V ⊕ Finset V) where
  Adj x y := ∃ v ∈ s.Bgood,
    (x = Sum.inl (s.P v) ∧ y = Sum.inr (s.D v)) ∨
    (y = Sum.inl (s.P v) ∧ x = Sum.inr (s.D v))
  symm := ⟨by intro x y; aesop⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def pdVertices (P0 D0 : Finset (Finset V)) : Finset (Finset V ⊕ Finset V) := by
  classical
  exact P0.image Sum.inl ∪ D0.image Sum.inr

abbrev PDVertex (P0 D0 : Finset (Finset V)) := {x : Finset V ⊕ Finset V // x ∈ pdVertices P0 D0}

def delta (C0 : ℕ) : ℕ := ⌈Real.rpow ((C0 : ℝ) ^ 4) (1 / 3)⌉₊

def selectedGood {C0 : ℕ} {F : SimpleGraph V} (s : CanonicalData C0 F)
    (P0 D0 : Finset (Finset V)) : Finset V := by
  classical
  exact s.Bgood.filter (fun v => s.P v ∈ P0 ∧ s.D v ∈ D0)

/-- A0 distinguishes the family in both directions, as supplied by Lemma 11. -/
def DualDistinguishes (ℋ : Finset (Finset V)) (A0 : Finset V) : Prop :=
  Set.InjOn (fun X : Finset V => X ∩ A0) (↑ℋ : Set (Finset V)) ∧
  Set.InjOn (fun x : V => ℋ.filter (fun X => x ∈ X)) (↑A0 : Set V)

/-- Section 3.2.3 selections. Tree, incidence, and distinguishing hypotheses are inputs;
landing, multiplication and stabilizer triviality are not. -/
structure FewChoices {C0 : ℕ} {F : SimpleGraph V} (s : CanonicalData C0 F) where
  few : s.defects.card < C0 ^ 2 * s.A.card
  P0 : Finset (Finset V)
  D0 : Finset (Finset V)
  P0_sub : P0 ⊆ s.profiles
  D0_sub : D0 ⊆ s.defects
  T : SimpleGraph (PDVertex P0 D0)
  T_sub : T ≤ (pdGraph s).induce (↑(pdVertices P0 D0) : Set (Finset V ⊕ Finset V))
  T_tree : T.IsTree
  min_degree : ∀ x : PDVertex P0 D0,
    delta C0 ≤ Nat.card (((pdGraph s).induce (↑(pdVertices P0 D0) : Set (Finset V ⊕ Finset V))).neighborSet x)
  max_degree : ∀ x : PDVertex P0 D0, Nat.card (T.neighborSet x) ≤ delta C0
  vP : {P : Finset V // P ∈ P0} → V
  uD : {D : Finset V // D ∈ D0} → V
  vP_mem : ∀ P, vP P ∈ selectedGood s P0 D0
  uD_mem : ∀ D, uD D ∈ selectedGood s P0 D0
  vP_profile : ∀ P, s.P (vP P) = P.val
  uD_defect : ∀ D, s.D (uD D) = D.val
  Apro : Finset V
  Adef : Finset V
  R0 : Finset V
  Apro_sub : Apro ⊆ s.Q
  Adef_sub : Adef ⊆ s.A \ s.Q
  Apro_size : Apro.card ≤ P0.card - 1
  Adef_size : Adef.card ≤ D0.card - 1
  pro_distinguishes : DualDistinguishes P0 Apro
  def_distinguishes : DualDistinguishes D0 Adef
  witness : s.Witness Adef R0
  R0_size : R0.card ≤ (s.representativesOf Adef).card - 1
  R0_diverse : Diverse F (s.representativesOf Adef) R0

namespace FewChoices
variable {C0 : ℕ} {F : SimpleGraph V} {s : CanonicalData C0 F}

def Bpro (f : FewChoices s) : Finset V := by
  classical
  exact Finset.univ.image f.vP

def Bdef (f : FewChoices s) : Finset V := by
  classical
  exact Finset.univ.image f.uD

/-- Every tree edge selects the good vertex having that profile/defect pair. -/
def Btree (f : FewChoices s) : Finset V := by
  classical
  exact s.Bgood.filter (fun v => ∃ (hp : Sum.inl (s.P v) ∈ pdVertices f.P0 f.D0)
    (hd : Sum.inr (s.D v) ∈ pdVertices f.P0 f.D0), f.T.Adj ⟨_, hp⟩ ⟨_, hd⟩)

def Q0 (f : FewChoices s) := s.representativesOf f.Adef
def B0 (f : FewChoices s) := selectedGood s f.P0 f.D0
def Aprime (f : FewChoices s) := f.Apro ∪ f.Adef ∪ f.Q0
def Bprime (f : FewChoices s) := f.B0 ∪ f.R0
def Bcore (f : FewChoices s) := f.Bpro ∪ f.Bdef ∪ f.Btree ∪ f.R0
def nprime (f : FewChoices s) := 2 * (f.P0.card + f.D0.card)

def InH0 (f : FewChoices s) (σ : CoreAut F f.Aprime f.Bcore) : Prop :=
  Preserves (ambientPerm σ) f.Bpro ∧ Preserves (ambientPerm σ) f.Bdef ∧
  Preserves (ambientPerm σ) f.Btree ∧ Preserves (ambientPerm σ) f.Apro ∧
  Preserves (ambientPerm σ) f.Adef ∧ Preserves (ambientPerm σ) f.Q0 ∧
  Preserves (ambientPerm σ) f.R0

/-- The raw profile/defect assignment. Its image is not assumed to lie in the tree. -/
def assignment (f : FewChoices s) (σ : CoreAut F f.Aprime f.Bcore)
    (x : PDVertex f.P0 f.D0) : Finset V ⊕ Finset V := by
  classical
  rcases x with ⟨P | D, hx⟩
  · have hp : P ∈ f.P0 := by simpa [pdVertices] using hx
    exact Sum.inl (s.P (ambientPerm σ (f.vP ⟨P, hp⟩)))
  · have hd : D ∈ f.D0 := by simpa [pdVertices] using hx
    exact Sum.inr (s.D (ambientPerm σ (f.uD ⟨D, hd⟩)))

end FewChoices
end SmallClassesNeighbourhood.Linear


