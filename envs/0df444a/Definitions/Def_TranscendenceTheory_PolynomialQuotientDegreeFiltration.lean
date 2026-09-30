-- Prove2me | Definitions.Def_TranscendenceTheory_PolynomialQuotientDegreeFiltration
-- name    : TranscendenceTheory_PolynomialQuotientDegreeFiltration
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T05:12:54.242126+00:00
-- url     : https://prove2.me/theorems/e136bb29-efec-4269-abf6-ae1028a19e22
-- title:
--   Polynomial quotient images of bounded total degree
-- statement:
--   For a polynomial ideal I over a field K, quotientDegreeImage I n is the image in R/I of the K-vector space of polynomials of total degree at most n.
--
--   $$
--   F_n(I)=\operatorname{im}(R_{\le n}\to R/I).
--   $$
--
--   It is a submodule of the actual ideal quotient, preserving all nilpotent information. For finitely many variables it is finite-dimensional regardless of whether the full quotient is finite-dimensional. The definition includes that finite-module instance. It imposes no rank stabilization, zero-set, or generator-degree hypothesis.
-- source:
--   Luca Chiantini and Juan Migliore, Almost maximal growth of the Hilbert function, Lemma 4.11, p. 20, https://academicweb.nd.edu/~jmiglior/CM2.pdf. The length-minus-one interpolation argument is formalized in affine degree-filtration form: an equality of consecutive ranks makes the earlier polynomial image invariant under multiplication by every variable and hence equal to the full quotient. Before stabilization, dimensions increase strictly from the constant class, forcing saturation by degree D-1 for a quotient of dimension D. The formal proof works over any field and includes nonradical ideals and the zero quotient; it does not formalize the source's sheaf-cohomology statement. Applied to A.1, it gives an equivalent bounded-degree rank certificate for each quotient dimension, retaining the same geometric data, local lengths and constant. The uniform rank estimate and geometric witness selection remain open.

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace TranscendenceTheory

/-- Classes represented by polynomials of total degree at most n. -/
def quotientDegreeImage {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) : Submodule K (MvPolynomial σ K ⧸ I) :=
  (MvPolynomial.restrictTotalDegree σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap

instance quotientDegreeImage_finite {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) : Module.Finite K (quotientDegreeImage I n) :=
  Module.Finite.map _ _

end TranscendenceTheory


