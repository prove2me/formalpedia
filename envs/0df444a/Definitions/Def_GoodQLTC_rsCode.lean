-- Prove2me | Definitions.Def_GoodQLTC_rsCode
-- name    : GoodQLTC_rsCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:34.21147+00:00
-- url     : https://prove2.me/theorems/82b79035-d373-4734-a57d-ffb78f80a421
-- title:
--   Reed–Solomon codes $\mathrm{RS}_F(\Omega,u)$ and monomial changes of coordinates
-- statement:
--   For $\Omega\subseteq F$ and $0\le u\le|\Omega|$,
--   $$
--   \mathrm{RS}_F(\Omega,u)=\{(P(z))_{z\in\Omega}:P\in F[X],\ \deg P<u\},\qquad \mathrm{RS}_F(\Omega,0)=0 .
--   $$
--   A **monomial change of coordinates** permutes the coordinates and multiplies each coordinate by a nonzero scalar.
--
--   **Formalization Note** The image of $F[X]_{<u}$ under evaluation; a monomial change is $x\mapsto(\omega\mapsto c(\omega)x(\sigma\omega))$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §13, p.48 (PDF p.51)

import Mathlib

namespace GoodQLTC

/-- Evaluation of a polynomial at the points of `Ω ⊆ F`, as an `F`-linear map `F[X] → F^Ω`. -/
noncomputable def evalOn {F : Type} [Field F] (Ω : Set F) : Polynomial F →ₗ[F] (Ω → F) where
  toFun P z := P.eval z.1
  map_add' P Q := by
    ext z
    simp
  map_smul' c P := by
    ext z
    simp only [Polynomial.eval_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]

/-- The **Reed–Solomon code** `RS_F(Ω, u) := {(P(z))_{z∈Ω} : P ∈ F[X], deg P < u}` on an
evaluation set `Ω ⊆ F`, Gay–Jeronimo, arXiv:2609.20780 (held version), §13, p.48; for `u = 0` it
is `0`. **Formalization Note.** The image of `F[X]_{<u}` (`Polynomial.degreeLT`) under evaluation
at the points of the subtype `Ω`. -/
noncomputable def rsCode {F : Type} [Field F] (Ω : Set F) (u : ℕ) : Submodule F (Ω → F) :=
  (Polynomial.degreeLT F u).map (evalOn Ω)

/-- The linear map `x ↦ (ω ↦ c(ω) x(σ ω))` of a monomial change of coordinates. -/
def monomialMap {F : Type} [Field F] {Ω : Type} (σ : Equiv.Perm Ω) (c : Ω → Fˣ) :
    (Ω → F) →ₗ[F] (Ω → F) where
  toFun x ω := (c ω : F) * x (σ ω)
  map_add' x y := by
    ext ω
    simp [mul_add]
  map_smul' a x := by
    ext ω
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- A **monomial change of coordinates** of a code `C ⊆ F^Ω` (arXiv:2609.20780, §13, p.48): it
permutes the coordinates by `σ` and multiplies each coordinate by a nonzero scalar `c(ω)`; the
image of `C` is `{ω ↦ c(ω) x(σ ω) : x ∈ C}`. -/
def monomialImage {F : Type} [Field F] {Ω : Type} (σ : Equiv.Perm Ω) (c : Ω → Fˣ)
    (C : Submodule F (Ω → F)) : Submodule F (Ω → F) :=
  C.map (monomialMap σ c)

end GoodQLTC


