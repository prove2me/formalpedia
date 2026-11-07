-- Prove2me | Definitions.Def_ModFormPIR_Witness
-- name    : ModFormPIR_Witness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:00:03.330288+00:00
-- url     : https://prove2.me/theorems/94b6eaf6-09fd-4647-aab1-3b498e940f3f
-- title:
--   The dual witness, $P_\beta$, $F_g$, $A_m$, $B$, $\ell_g$ and $H_g$
-- statement:
--   For $\beta:\mathbb Z_q^d\to\mathbb C$, conditions (42)–(44) are $\beta_0=1$; $\beta_x=0$ unless $\sum_ix_i=0$; and $\beta_x=\beta_{x+\mathbf 1}$. Condition (45) at $a$ on $T$ is $\sum_x\beta_x\zeta_q^{a\langle x,x\rangle+\langle x,z\rangle}=0$ for all $z\in T$.
--
--   From $\beta$ one forms the polynomial $P_\beta(X)=\sum_x\beta_x\prod_iX_{x_i}$ and $F_g(\tau,z)=P_\beta(\rho(g)\Theta(\tau,z/q))$, with $F=F_I$. Then:
--
--   1. $A_j(\tau)=\frac1{j!}\partial_z^jF(\tau,z)|_{z=0}$, and $m$ is minimal with $A_m\not\equiv0$;
--   2. $B_{x,y}(\tau)=\exp(\pi idx^2\tau/(4q))F(\tau,(x\tau+y)/2)$ and $B=B_{0,1}B_{1,0}B_{1,1}$;
--   3. $\Phi_{g,\ell}(w)$ is the coefficient of $e^{\pi i\tau\ell/(4q)}$ in $P_\beta(\rho(g)\Theta(\tau,w))$, and $\ell_g=(\ell^*-d)/8$ with $\ell^*$ minimal such that $\Phi_{g,\ell^*}\not\equiv0$;
--   4. $H_g=\min\{\sum_iw_q(x_i):[X_{x_1}\cdots X_{x_d}](P_\beta\circ\rho(g))\ne0\}$.
--
--   The file also defines $\alpha^{(J)}$ of Definition 12.5 and the lifts of the selected cusp matrices. These build the two scalar forms whose orders at cusps contradict the valence formula.
--
--   **Formalization Note** The paper's $\beta$ comes from a contradiction hypothesis, so these objects are defined for every $\beta$. $\Phi_{g,\ell}$ is the finite sum over $k\in\mathbb Z^d$ with $\sum_i(2k_i-1)^2=\ell$. $H_g$ reads a monomial coefficient of a commutative polynomial.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Definition 12.5, Proposition 12.7, Definition 12.8, pp.67–68; Definition 12.17, p.71; Lemma 12.24, Definitions 12.25–12.27, 12.30, pp.72–74

import Mathlib
import Definitions.Def_ModFormPIR_Expansion
import Definitions.Def_ModFormPIR_Weil

open Complex Matrix
open scoped UpperHalfPlane
open scoped BigOperators MatrixGroups Real

set_option autoImplicit false

namespace ModFormPIR

/-!
# The dual witness and the scalarizations built from it

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Definition 12.5, Proposition 12.7, Definitions 12.8, 12.17, pp.67–71;
Lemma 12.24, Definitions 12.25–12.27, 12.30, pp.72–74.

**Formalization Note.** The paper builds these objects from a witness `β` that Theorem 12.2 proves nonexistent, so they
are defined here for an arbitrary `β : ℤ_q^d → ℂ`. The expansion functions `Φ_{g,ℓ}` of (48) are defined by the
finite sum over `k ∈ ℤ^d` with `∑_i (2k_i - 1)² = ℓ` that the expansion yields. `H_g` reads the coefficient of a monomial
of the commutative polynomial `P_β ∘ ρ(g)`, as `MvPolynomial`.
-/

variable {q d : ℕ} [NeZero q]

/-- (42)–(44): `β_0 = 1`, `β_x = 0` unless `∑_i x_i = 0`, and `β_x = β_{x+𝟏}`. -/
structure IsNormalizedWitness (β : (Fin d → ZMod q) → ℂ) : Prop where
  zero : β 0 = 1
  support : ∀ x, ∑ i, x i ≠ 0 → β x = 0
  shift : ∀ x, β x = β (fun i => x i + 1)

/-- (45) at `a` on `T`: `∑_x β_x ζ_q^{a⟨x,x⟩ + ⟨x,z⟩} = 0` for all `z ∈ T`. -/
def IsOrthogonalOn (β : (Fin d → ZMod q) → ℂ) (a : ZMod q) (T : Set (Fin d → ZMod q)) : Prop :=
  ∀ z ∈ T, ∑ x : Fin d → ZMod q, β x * zq q (a * (x ⬝ᵥ x) + x ⬝ᵥ z) = 0

/-- Definition 12.5: `α^{(J)}_x = 1[∑x_i = 0] ζ_q^{-Jx_1} (1/q) ∑_b ζ_q^{-Jb} α_{x+b𝟏}`, where `x_1` is the coordinate
`i₀`. -/
noncomputable def alphaJ (i₀ : Fin d) (α : (Fin d → ZMod q) → ℂ) (J : ZMod q)
    (x : Fin d → ZMod q) : ℂ :=
  (if ∑ i, x i = 0 then 1 else 0) * zq q (-J * x i₀) * (1 / (q : ℂ)) *
    ∑ b : ZMod q, zq q (-J * b) * α (fun i => x i + b)

/-- Definition 12.8: `P_β(X) = ∑_x β_x ∏_i X_{x_i}`. -/
noncomputable def Pbeta (β : (Fin d → ZMod q) → ℂ) (X : ZMod q → ℂ) : ℂ :=
  ∑ x : Fin d → ZMod q, β x * ∏ i, X (x i)

/-- `F = F_I` (Definition 12.17): `F(τ,z) = P_β(Θ(τ,z/q))`. -/
noncomputable def Fid (β : (Fin d → ZMod q) → ℂ) (τ : ℍ) (z : ℂ) : ℂ :=
  Pbeta β (Theta q τ (z / q))

/-- Definition 12.17: `F_g(τ,z) = P_β(ρ(g)Θ(τ,z/q))`. -/
noncomputable def Fg (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (β : (Fin d → ZMod q) → ℂ)
    (g : SL(2, ℤ)) (τ : ℍ) (z : ℂ) : ℂ :=
  Pbeta β ((ρ g).mulVec (Theta q τ (z / q)))

/-- Definition 12.27: the `j`-th Taylor coefficient `(1/j!) ∂_z^j F(τ,z)|_{z=0}`. -/
noncomputable def taylorA (β : (Fin d → ZMod q) → ℂ) (j : ℕ) (τ : ℍ) : ℂ :=
  iteratedDeriv j (fun z => Fid β τ z) 0 / (Nat.factorial j : ℂ)

/-- Definition 12.27: `m` is the minimal index with `A_m ≢ 0`. -/
def IsTaylorOrder (β : (Fin d → ZMod q) → ℂ) (m : ℕ) : Prop :=
  (∃ τ, taylorA β m τ ≠ 0) ∧ ∀ j < m, ∀ τ, taylorA β j τ = 0

/-- The coefficient of the ordered tuple `r` in `P_β ∘ R`: `∑_x β_x ∏_i R_{x_i, r_i}`. -/
noncomputable def tupleCoeff (R : Matrix (ZMod q) (ZMod q) ℂ) (β : (Fin d → ZMod q) → ℂ)
    (r : Fin d → ZMod q) : ℂ :=
  ∑ x : Fin d → ZMod q, β x * ∏ i, R (x i) (r i)

/-- Lemma 12.24, (48): `Φ_{g,ℓ}(w) = ∑_{k ∈ ℤ^d, ∑(2k_i-1)²=ℓ} (-1)^{∑k_i} e^{2πi∑(k_i-1/2)w} C_g(k + (q-1)/2)`, the coefficient
of `e^{πiτℓ/(4q)}` in `P_β(ρ(g)Θ(τ,w))`, a finite sum. -/
noncomputable def Phi (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (β : (Fin d → ZMod q) → ℂ)
    (g : SL(2, ℤ)) (l : ℕ) (w : ℂ) : ℂ :=
  ∑ᶠ k : {k : Fin d → ℤ // ∑ i, (2 * k i - 1) ^ 2 = (l : ℤ)},
    (-1 : ℂ) ^ (∑ i, k.1 i) *
      exp (2 * π * I * (∑ i, ((k.1 i : ℂ) - 1 / 2)) * w) *
      tupleCoeff (ρ g) β (fun i => thetaIndex q (k.1 i))

/-- The levels `ℓ ≥ d`, `ℓ ≡ d (mod 8)`, at which `Φ_{g,ℓ} ≢ 0`. -/
def liveLevels (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (β : (Fin d → ZMod q) → ℂ)
    (g : SL(2, ℤ)) : Set ℕ :=
  {l | d ≤ l ∧ l ≡ d [MOD 8] ∧ ∃ w, Phi ρ β g l w ≠ 0}

/-- Definition 12.25: `ℓ_g = (ℓ* - d)/8`, with `ℓ*` the least live level. -/
noncomputable def ellG (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (β : (Fin d → ZMod q) → ℂ)
    (g : SL(2, ℤ)) : ℝ :=
  (((sInf (liveLevels ρ β g) : ℕ) : ℝ) - d) / 8

/-- `P_β ∘ R` as a polynomial in the variables `X_0, …, X_{q-1}`. -/
noncomputable def PbetaPoly (R : Matrix (ZMod q) (ZMod q) ℂ) (β : (Fin d → ZMod q) → ℂ) :
    MvPolynomial (ZMod q) ℂ :=
  ∑ x : Fin d → ZMod q, MvPolynomial.C (β x) *
    ∏ i, ∑ r : ZMod q, MvPolynomial.C (R (x i) r) * MvPolynomial.X r

/-- The exponent vector of the monomial `X_{x_1} ⋯ X_{x_d}`. -/
noncomputable def monomialOf (x : Fin d → ZMod q) : ZMod q →₀ ℕ :=
  ∑ i, Finsupp.single (x i) 1

/-- Definition 12.26: `H_g = min{∑_i w_q(x_i) : [X_{x_1}⋯X_{x_d}](P_β∘ρ(g)) ≠ 0}`. -/
noncomputable def HG (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (β : (Fin d → ZMod q) → ℂ)
    (g : SL(2, ℤ)) : ℝ :=
  sInf {v : ℝ | ∃ x : Fin d → ZMod q,
    MvPolynomial.coeff (monomialOf x) (PbetaPoly (ρ g) β) ≠ 0 ∧ v = ∑ i, cost q (1 / 2) (x i)}

/-- Definition 12.30 at `g = I`: `B_{x,y}(τ) = exp(πidx²τ/(4q)) F(τ,(xτ+y)/2)`. -/
noncomputable def Bxy (β : (Fin d → ZMod q) → ℂ) (x y : ℕ) (τ : ℍ) : ℂ :=
  exp (π * I * d * (x : ℂ) ^ 2 * τ / (4 * q)) * Fid β τ (((x : ℂ) * τ + y) / 2)

/-- Definition 12.30: `B = B_{0,1} B_{1,0} B_{1,1}`. -/
noncomputable def Bprod (β : (Fin d → ZMod q) → ℂ) (τ : ℍ) : ℂ :=
  Bxy β 0 1 τ * Bxy β 1 0 τ * Bxy β 1 1 τ

/-- The selected lift of Lemmas 12.35, 12.40: `g ≡ [2aλ, -λ⁻¹; λ, 0] (mod q)`, with `λ ∈ {1, …, (q-1)/2}`. -/
def IsSelectedLift (a : ZMod q) (lam : ℕ) (g : SL(2, ℤ)) : Prop :=
  1 ≤ lam ∧ lam ≤ (q - 1) / 2 ∧
    ((g 0 0 : ℤ) : ZMod q) = 2 * a * (lam : ZMod q) ∧
    ((g 0 1 : ℤ) : ZMod q) = -(lam : ZMod q)⁻¹ ∧
    ((g 1 0 : ℤ) : ZMod q) = (lam : ZMod q) ∧
    ((g 1 1 : ℤ) : ZMod q) = 0

end ModFormPIR


