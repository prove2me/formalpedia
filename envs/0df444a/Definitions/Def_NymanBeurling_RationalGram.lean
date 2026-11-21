-- Prove2me | Definitions.Def_NymanBeurling_RationalGram
-- name    : NymanBeurling_RationalGram
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T03:39:24.687468+00:00
-- url     : https://prove2.me/theorems/b5f89664-d8c9-48d2-a1d6-89e66599ae09
-- title:
--   Finite rational Gram matrices for the discrete Bagchi approximation problem
-- statement:
--   Column $i$ is the Bagchi sawtooth at denominator $i+2$ and row $n$ evaluates at $m=n+1$. The row weight is $1/[m(m+1)]$. Form the weighted Gram matrix of the first $D$ columns using the first $H$ rows, the column of inner products with the constant target, and the augmented Gram matrix with that target appended. The quotient of their determinants is a rational number. The canonical polynomial row cutoff is $(D+2)^4$. A finite certificate adds the elementary coefficient-mass tail bound to a finite prefix of the squared residual.
-- source:
--   Discrete Nyman–Beurling criterion in B. Bagchi, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146. Finite rational cost as in NymanBeurling.arbitrarily_small_remainder_certificates.

import Mathlib

open Finset Matrix
namespace NymanBeurling.RationalGram

/-- Row zero corresponds to the first Bagchi summand. -/
def weight (n : ℕ) : ℚ := 1 / ((n+1 : ℚ)*(n+2 : ℚ))
def atom (i n : ℕ) : ℚ := (((n+1)%(i+2) : ℕ):ℚ)/(i+2 : ℚ)
def residual (c : ℕ →₀ ℚ) (m : ℕ) : ℚ :=
  1 - ∑ i∈c.support,c i * ((m%(i+2) : ℕ):ℚ)/((i+2 : ℕ):ℚ)
def headEnergy (c : ℕ →₀ ℚ) (H : ℕ) : ℚ :=
  ∑ n∈range H, (residual c (n+1))^2 / ((n+1 : ℚ)*(n+2 : ℚ))
def mass (c : ℕ →₀ ℚ) : ℚ := 1 + ∑ i∈c.support,|c i|
def cost (c : ℕ →₀ ℚ) (H : ℕ) : ℚ := headEnergy c H + (mass c)^2/(H+1:ℚ)
def SmallCertificates : Prop := ∀ J : ℕ, ∃ (c : ℕ →₀ ℚ) (H : ℕ), cost c H < 1/(J+1:ℚ)

def design (D H : ℕ) : Matrix (Fin H) (Fin D) ℚ := Matrix.of (fun n i => atom i n)
def gram (D H : ℕ) : Matrix (Fin D) (Fin D) ℚ :=
  (design D H).transpose * Matrix.diagonal (fun n : Fin H => weight n) * design D H
def target (D H : ℕ) : Fin D → ℚ :=
  (design D H).transpose *ᵥ (fun n : Fin H => weight n)
def augmented (D H : ℕ) : Matrix (Fin D ⊕ Unit) (Fin D ⊕ Unit) ℚ :=
  Matrix.fromBlocks (gram D H) (Matrix.of fun i _ => target D H i)
    (Matrix.of fun _ i => target D H i) (Matrix.of fun _ _ => ∑ n : Fin H, weight n)
noncomputable def gap (D H : ℕ) : ℚ := (augmented D H).det/(gram D H).det
def rows (D : ℕ) : ℕ := (D+2)^4

end NymanBeurling.RationalGram


