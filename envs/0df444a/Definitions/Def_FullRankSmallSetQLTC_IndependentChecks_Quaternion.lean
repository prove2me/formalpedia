-- Prove2me | Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion
-- name    : FullRankSmallSetQLTC_IndependentChecks_Quaternion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:02.046963+00:00
-- url     : https://prove2.me/theorems/14a85c26-04de-45fe-94d6-23a9e4132cb0
-- title:
--   Integral quaternions, the 2-groups Ĝ_m ⊇ G_m, reduction π_m and Ramanujan Cayley graphs
-- statement:
--   For a commutative ring $R$, $L(R)=R+Ri+Rj+Rk$ with $i^2=j^2=k^2=ijk=-1$ and norm $N(a)=a\bar a=a_0^2+a_1^2+a_2^2+a_3^2$.
--
--   1. **Norm shells.** For $n\equiv1\pmod4$, $A(n)=\{a\in L(\mathbb Z):N(a)=n,\ a_0\text{ odd}\}/\{\pm1\}$, represented by the elements with $a_0>0$.
--   2. **The groups** (Definition 4.1). With $R_m=\mathbb Z/2^m\mathbb Z$ and $U_m=1+2L(R_m)$ (odd real part, even pure part), $\widehat G_m=U_m/R_m^\times$ and $G_m=\{[x]\in\widehat G_m:N(x)\equiv1\pmod 8\}$, for $m\ge3$.
--   3. **Reduction** $\pi_m$: reduce an integral quaternion $a\equiv1\pmod2$ modulo $2^m$ and pass to the quotient by scalars; $A^{(m)}_n=\pi_m(A(n))$, also viewed as a subset of $G_m$.
--   4. **Normal forms.** Dividing a representative by its odd real part gives the unique representative $1+2u$, $u=u_1i+u_2j+u_3k$, $u_t\in\mathbb Z/2^{m-1}\mathbb Z$; the code of $[x]$ is $u_1+2^{m-1}u_2+2^{2(m-1)}u_3$, and the code of $(g,j)\in G_m\times[n]$ is $\mathrm{code}(g)+2^{3(m-1)}j$. These codes are the input format of the polynomial-time statements.
--   5. **Cayley graphs** $\mathrm{Cay}(H;S)$ on a subgroup $H$: $g\sim k$ iff $g\ne k$ and $g^{-1}k\in S$ or $k^{-1}g\in S$.
--   6. A connected $k$-regular finite graph is **Ramanujan** if every adjacency eigenvalue $\lambda\ne\pm k$ has $|\lambda|\le2\sqrt{k-1}$. **Girth at least $b$** means every cycle has length at least $b$.
--
--   **Formalization Note** $L(R)$ is Mathlib's `ℍ[R]`. $U_m$ is the kernel of reduction to $L(\mathbb Z/2^{\min(m,1)})$ on the units of $L(R_m)$; $G_m$ is the image of the units whose norm is $\equiv1$ modulo $2^{\min(m,3)}$; both agree with Definition 4.1 for $m\ge3$, the only range the source uses. $\pi_m$ takes the value $1$ on integral quaternions not $\equiv1\pmod 2$, which the source never reduces. Eigenvalues are real eigenvalues of the real adjacency matrix (it is symmetric).
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), §4.1, pp. 18–19, Definition 4.1, eqs. (4.1)–(4.2) (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Graph

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Quaternion

/-! # Integral quaternions, the 2-groups `Ĝ_m ⊇ G_m`, reduction `π_m`, Cayley graphs (§4.1)

`L(R) = R + Ri + Rj + Rk` with `i² = j² = k² = ijk = −1` is Mathlib's `ℍ[R]`; the norm
`N(a) = a ā = a₀² + a₁² + a₂² + a₃²` is `Quaternion.normSq`. -/

/-- The quaternion with coordinates `(a, b, c, d)`. -/
def qmk {S : Type*} [CommRing S] (a b c d : S) : ℍ[S] := ⟨a, b, c, d⟩

@[simp] theorem qmk_re {S : Type*} [CommRing S] (a b c d : S) : (qmk a b c d).re = a := rfl
@[simp] theorem qmk_imI {S : Type*} [CommRing S] (a b c d : S) : (qmk a b c d).imI = b := rfl
@[simp] theorem qmk_imJ {S : Type*} [CommRing S] (a b c d : S) : (qmk a b c d).imJ = c := rfl
@[simp] theorem qmk_imK {S : Type*} [CommRing S] (a b c d : S) : (qmk a b c d).imK = d := rfl

/-- Coefficientwise application of a ring homomorphism `f : R → S`, a ring homomorphism
`L(R) → L(S)` (congruences are coefficientwise). -/
def qmap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : ℍ[R] →+* ℍ[S] where
  toFun x := qmk (f x.re) (f x.imI) (f x.imJ) (f x.imK)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/-! ## The norm shells `A(n)` -/

/-- §4.1, p. 18: `A(n) = {a ∈ L(ℤ) : N(a) = n, a₀ odd}/{±1}`, represented by the unique
representative of each class with positive real part (the real part is odd, hence nonzero). -/
def APos (n : ℕ) : Set ℍ[ℤ] :=
  {a | Quaternion.normSq a = (n : ℤ) ∧ Odd a.re ∧ 0 < a.re}

/-- The class of `a` modulo `±1`, written by its representative with positive real part
(`a` itself if `a₀ > 0`, else `−a`). On quaternions with odd real part this is the
multiplication-induced map on classes. -/
def sgnNorm (a : ℍ[ℤ]) : ℍ[ℤ] := if 0 < a.re then a else -a

/-! ## The groups `Ĝ_m ⊇ G_m` (Definition 4.1, p. 18) -/

/-- Reduction modulo `2^m`, `L(ℤ) → L(ℤ/2^mℤ)`. -/
def redZ (m : ℕ) : ℍ[ℤ] →+* ℍ[ZMod (2 ^ m)] := qmap (Int.castRingHom (ZMod (2 ^ m)))

/-- `U_m = 1 + 2L(R_m)`, `R_m = ℤ/2^mℤ`: the units of `L(R_m)` congruent to `1` modulo `2`
(odd real part, even pure part; for `m ≥ 1` every such quaternion is a unit). It is the kernel
of reduction to `L(ℤ/2^{min(m,1)}ℤ)`, which is `L(𝔽₂)` for `m ≥ 1`. -/
noncomputable def Um (m : ℕ) : Subgroup (ℍ[ZMod (2 ^ m)])ˣ :=
  (Units.map (qmap (ZMod.castHom (pow_dvd_pow 2 (min_le_left m 1))
    (ZMod (2 ^ min m 1)))).toMonoidHom).ker

/-- The scalar units `R_m^×` inside `L(R_m)^×`. -/
noncomputable def scalars (m : ℕ) : Subgroup (ℍ[ZMod (2 ^ m)])ˣ :=
  (Units.map (algebraMap (ZMod (2 ^ m)) ℍ[ZMod (2 ^ m)]).toMonoidHom).range

instance scalars_normal (m : ℕ) : (scalars m).Normal := by
  constructor
  rintro _ ⟨c, rfl⟩ g
  refine ⟨c, ?_⟩
  apply Units.ext
  change (algebraMap (ZMod (2 ^ m)) ℍ[ZMod (2 ^ m)] (c : ZMod (2 ^ m))) =
    (g : ℍ[ZMod (2 ^ m)]) * algebraMap (ZMod (2 ^ m)) ℍ[ZMod (2 ^ m)] (c : ZMod (2 ^ m)) * ↑g⁻¹
  rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

instance scalars_subgroupOf_normal (m : ℕ) : ((scalars m).subgroupOf (Um m)).Normal :=
  Subgroup.Normal.subgroupOf inferInstance _

/-- Definition 4.1: `Ĝ_m = U_m / R_m^×`. -/
noncomputable abbrev GHat (m : ℕ) := ↥(Um m) ⧸ ((scalars m).subgroupOf (Um m))

instance quat_finite (m : ℕ) : Finite ℍ[ZMod (2 ^ m)] :=
  Finite.of_equiv _ (Quaternion.equivTuple (ZMod (2 ^ m))).symm

noncomputable instance ghat_fintype (m : ℕ) : Fintype (GHat m) := Fintype.ofFinite _

/-- Elements of `U_m` whose norm is `≡ 1 (mod 2^{min(m,3)})`, i.e. `≡ 1 (mod 8)` for `m ≥ 3`. -/
noncomputable def Um8 (m : ℕ) : Subgroup ↥(Um m) :=
  ((Units.map (ZMod.castHom (pow_dvd_pow 2 (min_le_left m 3)) (ZMod (2 ^ min m 3))).toMonoidHom).comp
    ((Units.map (Quaternion.normSq : ℍ[ZMod (2 ^ m)] →*₀ ZMod (2 ^ m)).toMonoidHom).comp
      (Um m).subtype)).ker

/-- Definition 4.1: `G_m = {[x] ∈ Ĝ_m : N(x) ≡ 1 (mod 8)}` (for `m ≥ 3`; the class condition
means some representative has norm `≡ 1 (mod 8)`, which for odd scalars `c` is independent of the
representative since `c² ≡ 1 (mod 8)`). -/
noncomputable def Gm (m : ℕ) : Subgroup (GHat m) :=
  (Um8 m).map (QuotientGroup.mk' ((scalars m).subgroupOf (Um m)))

open Classical in
/-- §4.1, p. 19: the reduction `π_m` on integral quaternions congruent to `1` modulo `2`
(reduction modulo `2^m` followed by the quotient by scalars), with values in `Ĝ_m`. On integral
quaternions not congruent to `1 (mod 2)` (outside the source's domain) it is set to `1`. -/
noncomputable def pim (m : ℕ) (a : ℍ[ℤ]) : GHat m :=
  if h : ∃ u : ↥(Um m), (((u : (ℍ[ZMod (2 ^ m)])ˣ)) : ℍ[ZMod (2 ^ m)]) = redZ m a then
    (QuotientGroup.mk h.choose : GHat m)
  else 1

/-- `A_p^{(m)} = π_m(A(p))` (p. 19), more generally `π_m(A(n))`. -/
noncomputable def Ared (m n : ℕ) : Set (GHat m) := pim m '' APos n

/-- `A_p^{(m)}` as a subset of the group `G_m` (its elements lying in `G_m`). -/
noncomputable def AredG (m n : ℕ) : Set ↥(Gm m) := {g | (g : GHat m) ∈ Ared m n}

/-- The normal-form code of `[x] ∈ Ĝ_m` (pp. 18–19): dividing a representative by its (odd,
hence invertible) real part gives the unique representative `1 + 2u`,
`u = u₁i + u₂j + u₃k`, `u_t ∈ ℤ/2^{m−1}ℤ`; the code is `u₁ + 2^{m−1}u₂ + 2^{2(m−1)}u₃` with
`u_t ∈ [0, 2^{m−1})`. It is a bijection `Ĝ_m → [0, 2^{3(m−1)})` and the input format of all
polynomial-time statements about `G_m`. -/
noncomputable def nfCode (m : ℕ) (g : GHat m) : ℕ :=
  let u : ↥(Um m) := Classical.choose (QuotientGroup.mk_surjective g)
  let x : ℍ[ZMod (2 ^ m)] := ((u : (ℍ[ZMod (2 ^ m)])ˣ) : ℍ[ZMod (2 ^ m)])
  let y : ℍ[ZMod (2 ^ m)] := (x.re)⁻¹ • x
  y.imI.val / 2 + 2 ^ (m - 1) * (y.imJ.val / 2) + 2 ^ (2 * (m - 1)) * (y.imK.val / 2)

/-- The code of a vertex `(g, j)` of `G_m × [n]`: `nfCode g + 2^{3(m−1)} j`. -/
noncomputable def gmCellCode (m : ℕ) {n : ℕ} (v : Cell ↥(Gm m) (Fin n)) : ℕ :=
  nfCode m (v.grp : GHat m) + 2 ^ (3 * (m - 1)) * v.lab.val

/-! ## Cayley graphs and the Ramanujan property -/

/-- The Cayley graph `Cay(H; S)` on the vertices of a subgroup `H`: `g ∼ k` iff `g ≠ k` and
`g⁻¹k ∈ S` or `k⁻¹g ∈ S`. For an inverse-closed `S ∌ 1` this is the usual simple Cayley graph
with edges `g — gs`, `s ∈ S`. -/
def cayleyGraph {Γ : Type*} [Group Γ] (H : Subgroup Γ) (S : Set Γ) : SimpleGraph ↥H where
  Adj g k := g ≠ k ∧ ((g : Γ)⁻¹ * k ∈ S ∨ (k : Γ)⁻¹ * g ∈ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
/-- §4.1, p. 19: a connected `k`-regular finite graph is **Ramanujan** if every adjacency
eigenvalue `λ ≠ ±k` satisfies `|λ| ≤ 2√(k−1)`. -/
def IsRamanujan {V : Type*} [Fintype V] (Γ : SimpleGraph V) (k : ℕ) : Prop :=
  Γ.Connected ∧ Γ.IsRegularOfDegree k ∧
  ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (Γ.adjMatrix ℝ)) μ →
    μ = k ∨ μ = -(k : ℝ) ∨ |μ| ≤ 2 * Real.sqrt ((k : ℝ) - 1)

/-- The girth of `Γ` is at least `b`: every cycle has length `≥ b` (vacuous for forests). -/
def GirthAtLeast {V : Type*} (Γ : SimpleGraph V) (b : ℝ) : Prop :=
  ∀ (v : V) (c : Γ.Walk v v), c.IsCycle → b ≤ (c.length : ℝ)

end FullRankSmallSetQLTC.IndependentChecks


