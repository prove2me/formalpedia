-- Prove2me | Definitions.Def_IharaAmalgam
-- name    : IharaAmalgam
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/39e1182b-714a-5c5f-b665-f18952db7f71
-- title:
--   Amalgam of two copies of Γ0​(N) over Γ0​(Nq)
-- statement:
--   For natural numbers $N,q$ this module constructs the amalgamated free product of two copies of $\Gamma_0(N)$ along $\Gamma_0(Nq)$, the two edge maps being the two standard ones. The $\mathrm{Fin}\,2$-indexed family `iharaEdge N q` is $![\iota_0, \iota_1]$, where $\iota_0 : \Gamma_0(Nq) \to \Gamma_0(N)$ is the subgroup inclusion and $\iota_1$ sends $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ to $\begin{pmatrix} a & bq \\ c/q & d\end{pmatrix}$, i.e. conjugation by $\mathrm{diag}(1,q)$ (the division is exact because $q \mid c$, and the resulting matrix again lies in $\Gamma_0(N)$). The amalgam itself, `iharaAmalgam N q`, is the type of Mathlib's monoid pushout `Monoid.PushoutI` of this family, carried over as a group. Accompanying it are the two vertex homomorphisms `iharaVertex N q i` from $\Gamma_0(N)$ to `iharaAmalgam N q` for $i \in \{0,1\}$, the edge homomorphism `iharaBase N q` from $\Gamma_0(Nq)$, and the identities `iharaVertex_zero_iota0`, `iharaVertex_one_iota1` and `iharaVertex_edge` expressing that the square commutes, i.e. that $\iota_0$ into the copy indexed $0$ and $\iota_1$ into the copy indexed $1$ become equal in the amalgam.
--
--   The second half records the universal property in the shape needed later. Given monoid homomorphisms $f_0, f_1 : \Gamma_0(N) \to K$ with $f_0 \circ \iota_0 = f_1 \circ \iota_1$, `iharaLift f₀ f₁ h` is the induced homomorphism `iharaAmalgam N q` $\to K$; its defining equations are `iharaLift_vertex` (together with the two specialisations giving $f_0$ and $f_1$ on the vertex copies) and `iharaLift_base`, which evaluates it on the edge subgroup as $f_0 \circ \iota_0$. The helpers `pairFamily` and `pairFamily_compat` package the pair $(f_0,f_1)$ and its compatibility as an indexed family. Finally `iharaAmalgam_hom_ext` states that two homomorphisms out of the amalgam agreeing after composition with both vertex maps are equal, and `iharaVertex_range_sup` that the two vertex images generate the whole amalgam. All declarations are total in $N$ and $q$; no injectivity or surjectivity of any comparison with a group of matrices is asserted here.
--
--   **Relation to Mathlib.** Built directly on Mathlib's `Monoid.PushoutI` for an indexed family of homomorphisms from a common base: `iharaAmalgam` is that pushout for the two-element family $![\iota_0,\iota_1]$, with the lifting, extensionality and induction principles inherited from it. Mathlib has no amalgam of congruence subgroups; the edge maps $\iota_0,\iota_1$ on $\Gamma_0(Nq)$ are the project's own.
--
--   **Where it is used.** The amalgam is the group-theoretic side of Ihara's lemma: for $q$ prime and $q \nmid N$ one compares it with the congruence subgroup of $\mathrm{SL}_2(\mathbb{Z}[1/q])$ acting on the Bruhat–Tits tree, whose two vertex stabilisers are copies of $\Gamma_0(N)$ meeting in $\Gamma_0(Nq)$. That comparison feeds the level-raising step used in the Taylor–Wiles argument, where the lifting property `iharaLift` supplies maps out of the amalgam from pairs of compatible representations or Hecke actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_IharaAmalgam.lean

import Definitions.Def_IharaIota
import Mathlib.GroupTheory.PushoutI

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups

def iharaEdge (N q : ℕ) : Fin 2 → (Gamma0 (N * q) →* Gamma0 N) :=
  ![ι₀ N q, ι₁ N q]

@[simp] theorem iharaEdge_zero (N q : ℕ) : iharaEdge N q 0 = ι₀ N q := rfl

@[simp] theorem iharaEdge_one (N q : ℕ) : iharaEdge N q 1 = ι₁ N q := rfl

def iharaAmalgam (N q : ℕ) : Type :=
  Monoid.PushoutI (iharaEdge N q)

instance (N q : ℕ) : Group (iharaAmalgam N q) :=
  inferInstanceAs (Group (Monoid.PushoutI (iharaEdge N q)))

def iharaVertex (N q : ℕ) (i : Fin 2) : Gamma0 N →* iharaAmalgam N q :=
  Monoid.PushoutI.of (φ := iharaEdge N q) i

def iharaBase (N q : ℕ) : Gamma0 (N * q) →* iharaAmalgam N q :=
  Monoid.PushoutI.base (iharaEdge N q)

theorem iharaVertex_zero_iota0 (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 0 (ι₀ N q γ) = iharaBase N q γ :=
  Monoid.PushoutI.of_apply_eq_base (iharaEdge N q) 0 γ

theorem iharaVertex_one_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 1 (ι₁ N q γ) = iharaBase N q γ :=
  Monoid.PushoutI.of_apply_eq_base (iharaEdge N q) 1 γ

theorem iharaVertex_edge (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 0 (ι₀ N q γ) = iharaVertex N q 1 (ι₁ N q γ) := by
  rw [iharaVertex_zero_iota0, iharaVertex_one_iota1]

section Lift

variable {N q : ℕ} {K : Type*} [Monoid K]

def pairFamily (f₀ f₁ : Gamma0 N →* K) : (i : Fin 2) → (Gamma0 N →* K) :=
  ![f₀, f₁]

@[simp] theorem pairFamily_zero (f₀ f₁ : Gamma0 N →* K) : pairFamily f₀ f₁ 0 = f₀ := rfl

@[simp] theorem pairFamily_one (f₀ f₁ : Gamma0 N →* K) : pairFamily f₀ f₁ 1 = f₁ := rfl

theorem pairFamily_compat (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q)) :
    ∀ i : Fin 2, (pairFamily f₀ f₁ i).comp (iharaEdge N q i) = f₀.comp (ι₀ N q) := by
  intro i
  fin_cases i
  · rfl
  · exact h.symm

def iharaLift (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q)) :
    iharaAmalgam N q →* K :=
  Monoid.PushoutI.lift (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h)

theorem iharaLift_vertex (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (i : Fin 2) (g : Gamma0 N) :
    iharaLift f₀ f₁ h (iharaVertex N q i g) = pairFamily f₀ f₁ i g :=
  Monoid.PushoutI.lift_of (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h) g

theorem iharaLift_vertex_zero (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (g : Gamma0 N) : iharaLift f₀ f₁ h (iharaVertex N q 0 g) = f₀ g :=
  iharaLift_vertex f₀ f₁ h 0 g

theorem iharaLift_vertex_one (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (g : Gamma0 N) : iharaLift f₀ f₁ h (iharaVertex N q 1 g) = f₁ g :=
  iharaLift_vertex f₀ f₁ h 1 g

theorem iharaLift_base (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (γ : Gamma0 (N * q)) : iharaLift f₀ f₁ h (iharaBase N q γ) = f₀ (ι₀ N q γ) :=
  Monoid.PushoutI.lift_base (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h) γ

theorem iharaAmalgam_hom_ext {f g : iharaAmalgam N q →* K}
    (h : ∀ i : Fin 2, f.comp (iharaVertex N q i) = g.comp (iharaVertex N q i)) : f = g :=
  Monoid.PushoutI.hom_ext_nonempty h

end Lift

theorem iharaVertex_range_sup (N q : ℕ) :
    (iharaVertex N q 0).range ⊔ (iharaVertex N q 1).range = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using Monoid.PushoutI.induction_on with
  | of i g =>
    fin_cases i
    · exact Subgroup.mem_sup_left ⟨g, rfl⟩
    · exact Subgroup.mem_sup_right ⟨g, rfl⟩
  | base γ => exact Subgroup.mem_sup_left ⟨ι₀ N q γ, iharaVertex_zero_iota0 N q γ⟩
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy

end Ihara


