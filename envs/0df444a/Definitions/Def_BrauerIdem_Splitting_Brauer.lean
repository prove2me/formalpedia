-- Prove2me | Definitions.Def_BrauerIdem_Splitting_Brauer
-- name    : BrauerIdem_Splitting_Brauer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:28.140406+00:00
-- url     : https://prove2.me/theorems/95ab6388-a5ea-41fa-a74e-15124cc8e3e8
-- title:
--   §2.2–§3, pp. 3–8 — Brauer algebra B_n(δ) over ℚ(δ): diagrams, δ-loop product, ideals J_n(ℓ), 𝔖_n-orbit sums, the element u, the ring K
-- statement:
--   A Brauer diagram on $n$ strands pairs the $n$ upper nodes with the $n$ lower nodes in a perfect matching. A propagating line joins one upper and one lower node. Placing diagram $A$ above diagram $B$ gives a three-row graph. Its middle-only connected components are closed loops, and its outer endpoints determine a new diagram $C$. The product of the two basis diagrams is
--
--   $$
--   AB=\delta^{v(A,B)}C,
--   $$
--
--   where $v(A,B)$ counts the closed loops. The vector space $B_n$ consists of formal linear combinations of diagrams over $F=\mathbb Q(\delta)$. The ideal $J_n(\ell)$ is spanned by diagrams with at most $\ell$ propagating lines. Simultaneously relabelling both rows by $\mathfrak S_n$ defines diagram orbits and their unnormalised sums $D_O=\sum_{A\in O}A$.
--
--   For $n-\ell$ even, $u$ is the diagram with upper and lower cups at the consecutive pairs $(1,2),(3,4),\ldots,(n-\ell-1,n-\ell)$, and vertical lines elsewhere. The permitted coefficient set is
--
--   $$
--   K=\left\{f/g:f,g\in\mathbb Z[\delta],\ g\text{ monic},\ \deg f\leq\deg g\right\}\subseteq F.
--   $$
--
--   These definitions support the formalization of the paper's splitting idempotent and may be reused for other Brauer algebra identities.
--
--   **Formalization Note** Nodes are zero based in Lean, so the paper's pair $(2j+1,2j+2)$ is $(2j,2j+1)$. The product is an explicit bilinear function on diagram coefficients. The defining predicate for a composite uses graph connectivity; the loop count retains the factor $\delta^{v(A,B)}$. For parity-invalid parameters, the helper diagram $u$ defaults to the identity; all statements using its intended cup form assume $n-\ell$ even. Orbit sums use the unnormalised diagrams printed in Theorem 14.
-- source:
--   King, Martin, Parker, On central idempotents in the Brauer algebra, arXiv:1609.01183v1, pp. 3–5, §2.2–§2.3; p. 8, §3

import Mathlib

noncomputable section
open Classical

namespace BrauerIdem.Splitting

abbrev Node (n : ℕ) := Fin n ⊕ Fin n

/-- Pair partitions of the top and bottom nodes. -/
def Diagram (n : ℕ) := {m : Node n → Node n // Function.Involutive m ∧ ∀ x, m x ≠ x}

instance (n : ℕ) : Fintype (Diagram n) := by unfold Diagram; infer_instance
instance (n : ℕ) : DecidableEq (Diagram n) := Classical.decEq _

def propCount {n : ℕ} (A : Diagram n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, A.1 (.inl i) = .inr j)).card

def identity (n : ℕ) : Diagram n :=
  ⟨fun x => Sum.swap x, by intro x; cases x <;> rfl, by intro x; cases x <;> simp⟩

abbrev F := RatFunc ℚ
def δ : F := RatFunc.X
abbrev Br (n : ℕ) := Diagram n → F
def basis {n : ℕ} (A : Diagram n) : Br n := fun C => if C = A then 1 else 0

def outer {n : ℕ} : Node n → Fin 3 × Fin n
  | .inl i => (0, i)
  | .inr i => (2, i)

def upper {n : ℕ} : Node n → Fin 3 × Fin n
  | .inl i => (0, i)
  | .inr i => (1, i)

def lower {n : ℕ} : Node n → Fin 3 × Fin n
  | .inl i => (1, i)
  | .inr i => (2, i)

def stackEdge {n : ℕ} (A B : Diagram n) (x y : Fin 3 × Fin n) : Prop :=
  x ≠ y ∧ ((∃ a : Node n, upper a = x ∧ upper (A.1 a) = y) ∨
    (∃ b : Node n, lower b = x ∧ lower (B.1 b) = y))

def stackGraph {n : ℕ} (A B : Diagram n) : SimpleGraph (Fin 3 × Fin n) where
  Adj x y := stackEdge A B x y ∨ stackEdge A B y x
  symm := by
    constructor
    intro x y h; exact h.symm
  loopless := by
    constructor
    intro x h; rcases h with h | h <;> exact h.1 rfl

def loops {n : ℕ} (A B : Diagram n) : ℕ :=
  @Fintype.card {c : (stackGraph A B).ConnectedComponent //
    ∀ v : Fin 3 × Fin n, (stackGraph A B).connectedComponentMk v = c → v.1 = 1}
    (Fintype.ofFinite _)

def IsComposite {n : ℕ} (A B C : Diagram n) : Prop :=
  ∀ x y : Node n, x ≠ y →
    (C.1 x = y ↔ (stackGraph A B).Reachable (outer x) (outer y))

def basisMul {n : ℕ} (A B : Diagram n) : Br n :=
  fun C => if IsComposite A B C then δ ^ loops A B else 0

def bmul {n : ℕ} (x y : Br n) : Br n :=
  ∑ A : Diagram n, ∑ B : Diagram n, (x A * y B) • basisMul A B

def one (n : ℕ) : Br n := basis (identity n)

def Jideal (n l : ℕ) : Submodule F (Br n) :=
  Submodule.span F {x | ∃ A : Diagram n, propCount A ≤ l ∧ x = basis A}

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) : Node n ≃ Node n :=
  Equiv.sumCongr σ σ

private theorem relabel_one (n : ℕ) : relabel (1 : Equiv.Perm (Fin n)) = Equiv.refl (Node n) := by
  ext x; cases x <;> rfl

private theorem relabel_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    relabel (σ * τ) = (relabel τ).trans (relabel σ) := by
  ext x; cases x <;> simp [relabel]

def permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Diagram n) : Diagram n :=
  ⟨fun x => relabel σ (A.1 ((relabel σ).symm x)),
   by intro x; dsimp only; simp only [Equiv.symm_apply_apply]
      rw [A.2.1]; simp,
   by intro x h; apply A.2.2 ((relabel σ).symm x); apply (relabel σ).injective; simpa using h⟩

instance (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Diagram n) where
  smul := permute
  one_smul := by
    intro A; apply Subtype.ext; funext x
    change (relabel 1) (A.1 ((relabel 1).symm x)) = A.1 x
    rw [relabel_one]; rfl
  mul_smul := by
    intro σ τ A; apply Subtype.ext; funext x
    change (relabel (σ * τ)) (A.1 ((relabel (σ * τ)).symm x)) =
      (relabel σ) ((relabel τ) (A.1 ((relabel τ).symm ((relabel σ).symm x))))
    rw [relabel_mul]; rfl

abbrev Orbit (n : ℕ) := Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (Diagram n))
def OrbitIdx (n l : ℕ) := {O : Orbit n // propCount O.out ≤ l}
instance (n l : ℕ) : Fintype (OrbitIdx n l) := by unfold OrbitIdx; infer_instance
instance (n l : ℕ) : DecidableEq (OrbitIdx n l) := Classical.decEq _

def orbitSum {n : ℕ} (O : Orbit n) : Br n :=
  fun C => if (⟦C⟧ : Orbit n) = O then 1 else 0
def Xof {n l : ℕ} (c : OrbitIdx n l → F) : Br n :=
  ∑ O : OrbitIdx n l, c O • orbitSum O.1

private def pairNat (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

private theorem pairNat_involutive (i : ℕ) : pairNat (pairNat i) = i := by
  unfold pairNat
  split_ifs <;> omega

private theorem pairNat_lt (n l i : ℕ) (h : (n-l) % 2 = 0 ∧ i < n-l) :
    pairNat i < n-l := by
  unfold pairNat
  split_ifs <;> omega

private theorem pairNat_ne (i : ℕ) : pairNat i ≠ i := by
  unfold pairNat
  split_ifs <;> omega

private def cupIndex (n l : ℕ) (i : Fin n) : Fin n :=
  if h : (n - l) % 2 = 0 ∧ i.val < n - l then
    ⟨pairNat i.val, by have := pairNat_lt n l i.val h; omega⟩
  else i

private theorem cupIndex_involutive (n l : ℕ) : Function.Involutive (cupIndex n l) := by
  intro i
  apply Fin.ext
  by_cases h : (n-l) % 2 = 0 ∧ i.val < n-l
  · have hp := pairNat_lt n l i.val h
    simp [cupIndex, h, hp, pairNat_involutive]
  · simp [cupIndex, h]

private theorem cupIndex_ne (n l : ℕ) (i : Fin n)
    (h : (n-l) % 2 = 0 ∧ i.val < n-l) : cupIndex n l i ≠ i := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [cupIndex, h] at hv
  exact pairNat_ne i.val hv

private def cupMate (n l : ℕ) : Node n → Node n
  | .inl i => if (n-l) % 2 = 0 ∧ i.val < n-l then .inl (cupIndex n l i) else .inr i
  | .inr i => if (n-l) % 2 = 0 ∧ i.val < n-l then .inr (cupIndex n l i) else .inl i

private theorem cupIndex_lt (n l : ℕ) (i : Fin n)
    (h : (n-l) % 2 = 0 ∧ i.val < n-l) : (cupIndex n l i).val < n-l := by
  simpa [cupIndex, h] using pairNat_lt n l i.val h

private theorem cupMate_involutive (n l : ℕ) : Function.Involutive (cupMate n l) := by
  intro x
  cases x with
  | inl i =>
    by_cases h : (n-l) % 2 = 0 ∧ i.val < n-l
    · have hnext : (n-l) % 2 = 0 ∧ (cupIndex n l i).val < n-l := ⟨h.1, cupIndex_lt n l i h⟩
      simpa [cupMate, h, hnext] using cupIndex_involutive n l i
    · simp [cupMate, h]
  | inr i =>
    by_cases h : (n-l) % 2 = 0 ∧ i.val < n-l
    · have hnext : (n-l) % 2 = 0 ∧ (cupIndex n l i).val < n-l := ⟨h.1, cupIndex_lt n l i h⟩
      simpa [cupMate, h, hnext] using cupIndex_involutive n l i
    · simp [cupMate, h]

private theorem cupMate_ne (n l : ℕ) (x : Node n) : cupMate n l x ≠ x := by
  cases x with
  | inl i =>
    by_cases h : (n-l) % 2 = 0 ∧ i.val < n-l
    · simpa [cupMate, h] using cupIndex_ne n l i h
    · simp [cupMate, h]
  | inr i =>
    by_cases h : (n-l) % 2 = 0 ∧ i.val < n-l
    · simpa [cupMate, h] using cupIndex_ne n l i h
    · simp [cupMate, h]

def uDiag (n l : ℕ) : Diagram n :=
  ⟨cupMate n l, cupMate_involutive n l, cupMate_ne n l⟩

def Kring : Set F := {x | ∃ f g : Polynomial ℤ,
  g.Monic ∧ f.natDegree ≤ g.natDegree ∧
  x = algebraMap (Polynomial ℚ) F (f.map (Int.castRingHom ℚ)) /
      algebraMap (Polynomial ℚ) F (g.map (Int.castRingHom ℚ))}

def IsSplittingIdempotent {n : ℕ} (J : Submodule F (Br n)) (φ : Br n) : Prop :=
  φ - one n ∈ J ∧ ∀ d ∈ J, bmul φ d = 0 ∧ bmul d φ = 0

end BrauerIdem.Splitting


