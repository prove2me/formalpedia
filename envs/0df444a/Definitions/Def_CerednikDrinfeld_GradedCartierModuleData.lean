-- Prove2me | Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
-- name    : CerednikDrinfeld_GradedCartierModuleData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/faed270a-bdef-58d5-8fd3-f32b2c7e82a7
-- title:
--   Graded Cartier module data with a degree-one operator Π
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j \colon W(\mathbb{F}_{p^2}) \to B$ (written `Zp2 p` for the Witt vectors of the field with $p^2$ elements). The structure `GradedCartierModuleData` packages: a module $M$ over the Witt ring $W(B)$; two additive endomorphisms `frobenius` and `verschiebung` of $M$, written $F$ and $V$; a $W(B)$-linear endomorphism `varpi`, written $\Pi$; and a family `piece` of two $W(B)$-submodules $M_0, M_1$ indexed by `Fin 2`. The axioms are the Cartier relations $F(wx) = \sigma(w)F(x)$, $w\,V(x) = V(\sigma(w)x)$, $V(w\,F(x)) = {}^{V}\!w\cdot x$ and $F(V(x)) = p\,x$ (with $\sigma$ and ${}^{V}(\cdot)$ the Frobenius and Verschiebung of $W(B)$), the commutations $\Pi V = V\Pi$, $\Pi F = F\Pi$ and $\Pi^2 = p$, and the grading conditions: $M_0$ and $M_1$ are complementary (`IsCompl`), and each of $V$, $F$, $\Pi$ carries $M_i$ into $M_{i+1}$, the index running in `Fin 2` with its cyclic addition. Note that $V F = p$ is not imposed; the derived lemma `verschiebung_frobenius` gives instead $V(F(x)) = {}^{V}1\cdot x$.
--
--   On such a datum further notions are defined as predicates rather than fields. `homothety b` is multiplication by the Teichmüller lift $[b]$, for $b \in B$. `IsHomogeneousVBasis γ` asserts $\gamma_i \in M_i$ and that every $x \in M$ is written uniquely as $[c_0]\gamma_0 + [c_1]\gamma_1 + V y$ with $c_i \in B$, $y \in M$; from uniqueness, $V$ is injective (`IsHomogeneousVBasis.verschiebung_injective`). `IsVAdicallyComplete` asserts that for every sequence $(x_m)$ there is exactly one $s \in M$ with $s \equiv \sum_{m<N} V^m x_m \pmod{V^N M}$ for all $N$, and `IsSpecialCartierModule` is the conjunction of the existence of a homogeneous $V$-basis with this completeness. `HasStructureConstants γ a` expresses the congruences $\Pi\gamma_i \equiv \sum_{m<N} V^m([a_{m,i}]\gamma_{\,(m+i+1) \bmod 2}) \pmod{V^N M}$ for all $N$, the shifted index being `piIndex`; `hasStructureConstants_order_zero` records the vacuous case $N = 0$. Finally `IsBaseChangeAlong φ D D' f` says that the additive map $f \colon M \to M'$ is $W(\varphi)$-semilinear, commutes with $F$, $V$ and $\Pi$, preserves the two pieces, and carries some homogeneous $V$-basis of $M$ to a homogeneous $V$-basis of $M'$ — a property of $f$, not an assertion that $M'$ is a tensor product.
--
--   **Relation to Mathlib.** Mathlib supplies the Witt vectors $W(B)$ with their Frobenius, Verschiebung and Teichmüller maps, which are used here; it has no notion of Cartier or Dieudonné module, so the graded structure and the attendant predicates are the project's own.
--
--   **Where it is used.** These data are the linear-algebra counterpart of the special formal $\mathcal{O}_D$-modules defined alongside them, and serve as the Cartier-theoretic description used in the Čerednik–Drinfeld account of the $p$-adic uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_GradedCartierModuleData.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

structure GradedCartierModuleData (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B]
    (j : Zp2 p →+* B) : Type 1 where

  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module (WittVector p B) M]

  frobenius : M →+ M

  verschiebung : M →+ M

  varpi : M →ₗ[WittVector p B] M

  piece : Fin 2 → Submodule (WittVector p B) M

  frobenius_smul : ∀ (w : WittVector p B) (x : M),
    frobenius (w • x) = WittVector.frobenius w • frobenius x

  smul_verschiebung : ∀ (w : WittVector p B) (x : M),
    w • verschiebung x = verschiebung (WittVector.frobenius w • x)

  verschiebung_smul_frobenius : ∀ (w : WittVector p B) (x : M),
    verschiebung (w • frobenius x) = WittVector.verschiebung w • x

  frobenius_verschiebung : ∀ x : M, frobenius (verschiebung x) = (p : ℕ) • x

  varpi_verschiebung : ∀ x : M, varpi (verschiebung x) = verschiebung (varpi x)

  varpi_frobenius : ∀ x : M, varpi (frobenius x) = frobenius (varpi x)

  varpi_varpi : ∀ x : M, varpi (varpi x) = (p : ℕ) • x

  isCompl_piece : IsCompl (piece 0) (piece 1)

  verschiebung_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → verschiebung x ∈ piece (i + 1)

  frobenius_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → frobenius x ∈ piece (i + 1)

  varpi_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → varpi x ∈ piece (i + 1)

namespace GradedCartierModuleData

attribute [instance] GradedCartierModuleData.addCommGroup GradedCartierModuleData.module

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

def homothety (D : GradedCartierModuleData p B j) (b : B) : D.M →+ D.M :=
  DistribSMul.toAddMonoidHom D.M (WittVector.teichmuller p b)

@[simp] theorem homothety_apply (D : GradedCartierModuleData p B j) (b : B) (x : D.M) :
    D.homothety b x = WittVector.teichmuller p b • x := rfl

def piIndex (m : ℕ) (i : Fin 2) : Fin 2 := ⟨(m + i + 1) % 2, Nat.mod_lt _ two_pos⟩

def IsHomogeneousVBasis (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) : Prop :=
  (∀ i : Fin 2, γ i ∈ D.piece i) ∧
    ∀ x : D.M, ∃! cy : (Fin 2 → B) × D.M,
      x = (∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • γ i) + D.verschiebung cy.2

def IsVAdicallyComplete (D : GradedCartierModuleData p B j) : Prop :=
  ∀ x : ℕ → D.M, ∃! s : D.M, ∀ N : ℕ, ∃ t : D.M,
    s = (∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m] (x m)) + (⇑D.verschiebung)^[N] t

def IsSpecialCartierModule (D : GradedCartierModuleData p B j) : Prop :=
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ) ∧ D.IsVAdicallyComplete

def HasStructureConstants (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) : Prop :=
  ∀ (i : Fin 2) (N : ℕ), ∃ h : D.M,
    D.varpi (γ i) =
      (∑ m : Fin N, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) + (⇑D.verschiebung)^[N] h

def IsBaseChangeAlong {B' : Type} [CommRing B'] (φ : B →+* B')
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' (φ.comp j))
    (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧ D'.IsHomogeneousVBasis (fun i => f (γ i)))

theorem varpi_smul (D : GradedCartierModuleData p B j) (w : WittVector p B) (x : D.M) :
    D.varpi (w • x) = w • D.varpi x := map_smul _ _ _

theorem verschiebung_frobenius (D : GradedCartierModuleData p B j) (x : D.M) :
    D.verschiebung (D.frobenius x) = WittVector.verschiebung (1 : WittVector p B) • x := by
  rw [← D.verschiebung_smul_frobenius 1 x, one_smul]

theorem natCast_smul_eq_frobenius_verschiebung (D : GradedCartierModuleData p B j) (x : D.M) :
    (p : ℕ) • x = D.frobenius (D.verschiebung x) := (D.frobenius_verschiebung x).symm

theorem hasStructureConstants_order_zero (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) (i : Fin 2) :
    ∃ h : D.M, D.varpi (γ i) =
      (∑ m : Fin 0, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) + (⇑D.verschiebung)^[0] h :=
  ⟨D.varpi (γ i), by simp⟩

theorem IsHomogeneousVBasis.verschiebung_injective {D : GradedCartierModuleData p B j}
    {γ : Fin 2 → D.M} (h : D.IsHomogeneousVBasis γ) : Function.Injective D.verschiebung := by
  intro y y' hyy
  have key := h.2 (D.verschiebung y)
  obtain ⟨cy, hcy, huniq⟩ := key
  have h1 : ((fun _ => (0 : B)), y) = cy := huniq ((fun _ => (0 : B)), y) (by simp)
  have h2 : ((fun _ => (0 : B)), y') = cy := huniq ((fun _ => (0 : B)), y') (by simp [hyy])
  have := h1.trans h2.symm
  simpa using congrArg Prod.snd this

end GradedCartierModuleData

end CerednikDrinfeld

end


