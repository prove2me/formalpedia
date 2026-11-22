-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_StatementW
-- name    : Formalism_SubspaceCounting_StatementW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:08.044412+00:00
-- url     : https://prove2.me/theorems/f5e3af6c-5d0f-4d0a-bf41-55336de7dcec
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/StatementW.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.G0
open Polynomial in

def msMat {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
    ((g⁻¹ : GL (Fin r) L).1.map C)
open Polynomial in

def msDualMat {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  ((g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C)).transpose
def substS {K L ι : Type} [Field K] [Field L] [Algebra K L] [DecidableEq ι] {r : ℕ}
    (vec : ι → Bool) (S : Finset ι) (g : GL (Fin r) L) :
    MvPolynomial (ι × Fin r) K →ₐ[K] MvPolynomial (ι × Fin r) (Polynomial L) :=
  MvPolynomial.aeval fun p =>
    if p.1 ∈ S then
      (if vec p.1 then ∑ b, MvPolynomial.C ((msMat g) p.2 b) * MvPolynomial.X (p.1, b)
       else ∑ b, MvPolynomial.C ((msDualMat g) p.2 b) * MvPolynomial.X (p.1, b))
    else MvPolynomial.X p
def ValGE {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ} (vec : ι → Bool) (S : Finset ι) (d : ι → ℕ)
    (F : MvPolynomial (ι × Fin r) K) (th : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [Algebra K L] (g : GL (Fin r) L),
    MvPolynomial.C (Polynomial.X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i)) ∣
      substS (K := K) vec S g F
def MultiHom {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ} (F : MvPolynomial (ι × Fin r) K) (d : ι → ℕ) :
    Prop :=
  ∀ i, MvPolynomial.IsWeightedHomogeneous (fun p : ι × Fin r => if p.1 = i then 1 else 0) F (d i)
def detLetters {K ι : Type} [Field K] {r : ℕ} (A : Fin r → ι) : MvPolynomial (ι × Fin r) K :=
  Matrix.det (Matrix.of fun (l a : Fin r) => MvPolynomial.X (A l, a))
def DetDivides : Prop :=
  ∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (r : ℕ) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) K) (th : ℕ),
    Function.Injective A → (∀ l, A l ∈ S ∧ vec (A l) = true) → MultiHom G d →
    ValGE vec S d G th →
    (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) < th →
    (detLetters (K := K) A) ^ (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) ∣ G
def DetVal : Prop :=
  ∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (r : ℕ) (vec : ι → Bool)
    (S' : Finset ι) (A : Fin r → ι), 1 ≤ r → Function.Injective A →
    (∀ l, vec (A l) = true) →
    let dD : ι → ℕ := fun i => if i ∈ Set.range A then 1 else 0
    ((∀ l, A l ∈ S') → ValGE vec S' dD (detLetters (K := K) A) 1 ∧
        ¬ ValGE vec S' dD (detLetters (K := K) A) 2) ∧
      ((¬ ∀ l, A l ∈ S') → ¬ ValGE vec S' dD (detLetters (K := K) A) 1)
def CramerCofactor : Prop :=
  ∀ {R : Type} [CommRing R] (r : ℕ) (T : Matrix (Fin r) (Fin r) R) (σ : Fin r → R) (a : Fin r),
    σ a * T.det = ∑ l, (∑ b, T l b * σ b) * T.adjugate a l
end Formalism.G0


