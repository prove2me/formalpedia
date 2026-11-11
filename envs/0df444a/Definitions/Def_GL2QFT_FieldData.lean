-- Prove2me | Definitions.Def_GL2QFT_FieldData
-- name    : GL2QFT_FieldData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:20.142487+00:00
-- url     : https://prove2.me/theorems/01ba23c4-31aa-45ae-8d2b-217e2ef690fe
-- title:
--   Field data $D$: polynomial-basis models of $\mathbb F_q\subset\mathbb F_{q^2}$ and a primitive element $h$
-- statement:
--   The classical data $D$ of Remark 6.3. It consists of a prime $p$, an integer $r\ge1$ (so $q=p^r$ is an arbitrary prime power), a monic irreducible polynomial $f\in\mathbb F_p[X]$ of degree $r$, a monic irreducible quadratic $F\in\mathbb F_q[Y]$, and an element $h\in\mathbb F_{q^2}^*$ of multiplicative order $q^2-1$. The fields are the polynomial-basis models
--   $$\mathbb F_q=\mathbb F_p[X]/(f),\qquad \mathbb F_{q^2}=\mathbb F_q[Y]/(F).$$
--   The group of the mission is $G=\mathrm{GL}_2(\mathbb F_q)$, the generator of $\mathbb F_q^*$ is $g=h^{q+1}=N_{\mathbb F_{q^2}/\mathbb F_q}(h)$, and character labels are exponents: $X_q\cong\mathbb Z/(q-1)\mathbb Z$ and $X_{q^2}\cong\mathbb Z/(q^2-1)\mathbb Z$.
--
--   Every statement of the mission is quantified over all such data, so it holds for every prime power $q$, odd or even, prime or not, and for every choice of models and of $h$. Uniformity of circuits is relative to $D$, as Remark 6.3 prescribes.
--
--   **Formalization Note** $g$ is defined as the norm $N(h)=h\cdot h^q$, which is the paper's $h^{q+1}$ and lies in $\mathbb F_q$ by construction.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §6 p.34 ("Let q = p^r be a prime power"), Remark 6.2 and Remark 6.3, p.34 (PDF p.35); Appendix A p.79

import Mathlib

noncomputable section

namespace GL2QFT

open Polynomial

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Remark 6.3, p.34 (PDF p.35): the classical
data `D` of §6: "polynomial-basis models of `F_q ⊂ F_{q²}` and a primitive element `h ∈ F*_{q²}`".

* `p` is a prime and `r ≥ 1`, so `q = p^r` is an arbitrary prime power (§6, p.34: "Let `q = p^r`
  be a prime power");
* `f ∈ F_p[X]` is monic irreducible of degree `r`, and `F_q := F_p[X]/(f)` (`AdjoinRoot f`);
* `F ∈ F_q[Y]` is monic irreducible of degree `2`, and `F_{q²} := F_q[Y]/(F)`;
* `h ∈ F_{q²}` has multiplicative order `q² − 1`, i.e. generates `F*_{q²}`.

**Formalization Note** Every prime `p`, every `r ≥ 1` and every such pair of models is allowed;
nothing restricts to odd or prime `q`. The polynomial bases `1, X, …, X^{r-1}` of `F_q` over `F_p`
and `1, Y` of `F_{q²}` over `F_q` are the "polynomial-basis models"; they fix the input code of the
circuits (`GL2QFT.Codes`). -/
structure FieldData where
  /-- The characteristic `p`. -/
  p : ℕ
  /-- `p` is prime. -/
  hp : p.Prime
  /-- The degree `r` of `F_q` over `F_p`. -/
  r : ℕ
  /-- `r ≥ 1`. -/
  hr : 0 < r
  /-- The modulus of the polynomial-basis model of `F_q`. -/
  f : (ZMod p)[X]
  f_monic : f.Monic
  f_irr : Irreducible f
  f_deg : f.natDegree = r
  /-- The modulus of the polynomial-basis model of `F_{q²}` over `F_q`. -/
  F : (AdjoinRoot f)[X]
  F_monic : F.Monic
  F_irr : Irreducible F
  F_deg : F.natDegree = 2
  /-- The primitive element `h ∈ F*_{q²}`. -/
  h : AdjoinRoot F
  /-- `h` generates `F*_{q²}`: its order is `q² − 1`. -/
  h_order : orderOf h = (p ^ r) ^ 2 - 1

namespace FieldData

variable (D : FieldData)

instance instFactPrime : Fact D.p.Prime := ⟨D.hp⟩

instance instFactIrrF : Fact (Irreducible D.f) := ⟨D.f_irr⟩

/-- `q = p^r`, the order of `F_q`. -/
def q : ℕ := D.p ^ D.r

/-- The finite field `F_q`, the polynomial-basis model `F_p[X]/(f)`. -/
abbrev Fq : Type := AdjoinRoot D.f

instance instFactIrrFF : Fact (Irreducible D.F) := ⟨D.F_irr⟩

/-- The finite field `F_{q²}`, the polynomial-basis model `F_q[Y]/(F)`. -/
abbrev Fq2 : Type := AdjoinRoot D.F

instance instModuleFiniteFq : Module.Finite (ZMod D.p) D.Fq :=
  (AdjoinRoot.powerBasis' D.f_monic).finite

instance instFiniteFq : Finite D.Fq := Module.finite_of_finite (ZMod D.p)

instance instFintypeFq : Fintype D.Fq := Fintype.ofFinite _

instance instDecEqFq : DecidableEq D.Fq := Classical.decEq _

instance instModuleFiniteFq2 : Module.Finite D.Fq D.Fq2 :=
  (AdjoinRoot.powerBasis' D.F_monic).finite

instance instFiniteFq2 : Finite D.Fq2 := Module.finite_of_finite D.Fq

instance instFintypeFq2 : Fintype D.Fq2 := Fintype.ofFinite _

instance instDecEqFq2 : DecidableEq D.Fq2 := Classical.decEq _

/-- `q ≥ 2`. -/
theorem one_lt_q : 1 < D.q := Nat.one_lt_pow D.hr.ne' D.hp.one_lt

instance instNeZeroQSubOne : NeZero (D.q - 1) := ⟨by have := D.one_lt_q; omega⟩

instance instNeZeroQSqSubOne : NeZero (D.q ^ 2 - 1) :=
  ⟨by have := D.one_lt_q; have : D.q < D.q ^ 2 := by nlinarith
      omega⟩

/-- arXiv:2608.28573, §6, p.34: the group `G = GL₂(F_q)` of invertible `2 × 2` matrices over
`F_q`. A matrix `g` has entries `g 0 0 = a`, `g 0 1 = b`, `g 1 0 = c`, `g 1 1 = d` for the
paper's `g = (a b; c d)`. -/
abbrev G : Type := GL (Fin 2) D.Fq

/-- arXiv:2608.28573, Remark 6.3, p.34: the generator `g = h^{q+1}` of `F*_q`.

**Formalization Note** It is defined as the norm `N_{F_{q²}/F_q}(h)` (`Algebra.norm`), which is
`h · h^q = h^{q+1}` (Appendix A, p.79: `N(z) = z z̄`, `z̄ = z^q`) and lies in `F_q` by construction. -/
def gen : D.Fq := Algebra.norm D.Fq D.h

/-- Exponent labels of characters of `F*_q` (Remark 6.2, Appendix A p.79): `X_q ≅ Z/(q−1)Z`,
`α ↦ χ_α`. The label `0` is the trivial character, written "`α = 1`" in the paper. -/
abbrev Lab : Type := ZMod (D.q - 1)

/-- Exponent labels of characters of `F*_{q²}` (Appendix A, p.79, Definition 6.18): `X_{q²} ≅
Z/(q²−1)Z`, `k ↦ θ_k` with `θ_k(h) = e^{2πik/(q²−1)}`. -/
abbrev Lab2 : Type := ZMod (D.q ^ 2 - 1)

end FieldData

end GL2QFT


