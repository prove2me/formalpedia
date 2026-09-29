-- Prove2me | Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
-- name    : CerednikDrinfeld_EdgeFamilyConstants
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/bfde5373-57ab-5bf4-9499-ddd18eb592ca
-- title:
--   Witt branch constants and edge constants on edge charts
-- statement:
--   Fix a prime $p$. For an element $x$ of a commutative ring $R$, `wittDigit p x j` is the $j$-th Witt coefficient of $F[x]-[x]\in W(R)$, where $[\,\cdot\,]$ is the Teichmüller map and $F$ the Witt-vector Frobenius; in particular the $0$-th coefficient is $x^p-x$. From this the family `branchConstants p x : ℕ → R` is defined by cases on the index $m$: it is $x^p-x$ for $m=0$, it is $1$ for $m=1$, it is $\mathrm{wittDigit}\,p\,x\,(m/2)^{\,p^{m/2}}$ for even $m\ge 2$, and $0$ for odd $m\ge 3$. For a pair $(\xi,\eta)$ of elements of $R$, `edgeConstants p ξ η : ℕ → Fin 2 → R` is the two-branch family sending $(m,0)$ to the $m$-th branch constant of $\eta$ and $(m,1)$ to that of $\xi$; thus $a_{0,0}=\eta^p-\eta$, $a_{0,1}=\xi^p-\xi$ and $a_{1,i}=1$, as recorded by the accompanying simp lemmas. Two further groups of lemmas are established: if $\xi\eta=0$ then $a_{0,0}a_{0,1}=0$ (factoring $(\eta^p-\eta)(\xi^p-\xi)$ through $\xi\eta$), and this product equals $(p:R)$ whenever $p$ vanishes in $R$; and all three families commute with ring homomorphisms, $f(\mathrm{wittDigit}\,p\,x\,j)=\mathrm{wittDigit}\,p\,(f x)\,j$ and likewise for the branch and edge constants, so base change is evaluation.
--
--   The module then specialises to the standard edge chart in characteristic $p$: for a commutative ring $k$, `edgeRingCharP p k` is the edge-chart ring `FormalOmega.chartERing k (0 : k) p`, that is the localisation of $k[X_0,X_1]/(X_0X_1)$ away from the image of $(X_0^{p-1}-1)(X_1^{p-1}-1)$, with coordinates `edgeRingCharP.ξ` and `edgeRingCharP.η` satisfying $\xi\eta=0$. `edgeRingConstants p k` is the edge-constant family of this pair, and the final result states that when $k$ has characteristic $p$ the product of its two constants in degree $0$ equals $p$ in that ring. Nothing here asserts that these constants present any particular formal module; they are defined as an explicit family.
--
--   **Relation to Mathlib.** Witt vectors, the Teichmüller map and the Witt-vector Frobenius are Mathlib's; the branch and edge constant families, and the edge-chart ring they are evaluated on, are the project's own.
--
--   **Where it is used.** These are the candidate structure constants for Drinfeld's special formal module over the standard edge chart of the formal upper half-plane in characteristic $p$, entering the Cerednik–Drinfeld uniformisation of Shimura curves; the relation $a_{0,0}a_{0,1}=p$ reflects the nodal relation $\xi\eta=\pi$ degenerating at $\pi=0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_EdgeFamilyConstants.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld
namespace EdgeFamily

variable (p : ℕ) [Fact p.Prime]

def wittDigit {R : Type*} [CommRing R] (x : R) (j : ℕ) : R :=
  (WittVector.frobenius (WittVector.teichmuller p x) - WittVector.teichmuller p x).coeff j

def branchConstants {R : Type*} [CommRing R] (x : R) (m : ℕ) : R :=
  if m = 0 then x ^ p - x
  else if m = 1 then 1
  else if m % 2 = 0 then wittDigit p x (m / 2) ^ p ^ (m / 2)
  else 0

def edgeConstants {R : Type*} [CommRing R] (ξ η : R) : ℕ → Fin 2 → R :=
  fun m i => if i = 0 then branchConstants p η m else branchConstants p ξ m

variable {p}

@[simp] theorem branchConstants_zero {R : Type*} [CommRing R] (x : R) : branchConstants p x 0 = x ^ p - x := by
  simp [branchConstants]

@[simp] theorem branchConstants_one {R : Type*} [CommRing R] (x : R) : branchConstants p x 1 = 1 := by
  simp [branchConstants]

@[simp] theorem edgeConstants_zero_zero {R : Type*} [CommRing R] (ξ η : R) : edgeConstants p ξ η 0 0 = η ^ p - η := by
  simp [edgeConstants]

@[simp] theorem edgeConstants_zero_one {R : Type*} [CommRing R] (ξ η : R) : edgeConstants p ξ η 0 1 = ξ ^ p - ξ := by
  simp [edgeConstants]

@[simp] theorem edgeConstants_one {R : Type*} [CommRing R] (ξ η : R) (i : Fin 2) : edgeConstants p ξ η 1 i = 1 := by
  fin_cases i <;> simp [edgeConstants]

theorem edgeConstants_zero_zero_mul_zero_one {R : Type*} [CommRing R] (ξ η : R) (h : ξ * η = 0) :
    edgeConstants p ξ η 0 0 * edgeConstants p ξ η 0 1 = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  simp only [edgeConstants_zero_zero, edgeConstants_zero_one]
  have : (η ^ p - η) * (ξ ^ p - ξ) = (ξ * η) * ((η ^ n - 1) * (ξ ^ n - 1)) := by
    rw [hn]; ring
  rw [this, h, zero_mul]

theorem edgeConstants_zero_zero_mul_zero_one_eq_natCast {R : Type*} [CommRing R] (ξ η : R) (h : ξ * η = 0)
    (hp0 : (p : R) = 0) : edgeConstants p ξ η 0 0 * edgeConstants p ξ η 0 1 = (p : R) := by
  rw [edgeConstants_zero_zero_mul_zero_one ξ η h, hp0]

theorem wittDigit_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (j : ℕ) :
    f (wittDigit p x j) = wittDigit p (f x) j := by
  have h1 : WittVector.map f (WittVector.frobenius (WittVector.teichmuller p x)) =
      WittVector.frobenius (WittVector.map f (WittVector.teichmuller p x)) := by
    exact (WittVector.frobenius_isPoly p).map f _
  simp only [wittDigit]
  rw [← WittVector.map_coeff, map_sub, h1, WittVector.map_teichmuller]

theorem branchConstants_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (m : ℕ) :
    f (branchConstants p x m) = branchConstants p (f x) m := by
  simp only [branchConstants]
  split_ifs <;> simp [map_sub, map_pow, wittDigit_map]

theorem edgeConstants_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (ξ η : R) (m : ℕ) (i : Fin 2) :
    f (edgeConstants p ξ η m i) = edgeConstants p (f ξ) (f η) m i := by
  simp only [edgeConstants]
  split_ifs <;> exact branchConstants_map f _ m

variable (p)

abbrev edgeRingCharP (k : Type) [CommRing k] : Type := FormalOmega.chartERing k (0 : k) p

abbrev edgeRingCharP.ξ (k : Type) [CommRing k] : edgeRingCharP p k := FormalOmega.chartERing.ξ k (0 : k) p

abbrev edgeRingCharP.η (k : Type) [CommRing k] : edgeRingCharP p k := FormalOmega.chartERing.η k (0 : k) p

omit [Fact p.Prime] in
theorem edgeRingCharP.ξ_mul_η (k : Type) [CommRing k] : edgeRingCharP.ξ p k * edgeRingCharP.η p k = 0 := by
  rw [edgeRingCharP.ξ, edgeRingCharP.η, FormalOmega.chartERing.ξ_mul_η, map_zero]

abbrev edgeRingConstants (k : Type) [CommRing k] : ℕ → Fin 2 → edgeRingCharP p k :=
  edgeConstants p (edgeRingCharP.ξ p k) (edgeRingCharP.η p k)

theorem edgeRingConstants_mul (k : Type) [CommRing k] [CharP k p] :
    edgeRingConstants p k 0 0 * edgeRingConstants p k 0 1 = (p : edgeRingCharP p k) := by
  apply edgeConstants_zero_zero_mul_zero_one_eq_natCast _ _ (edgeRingCharP.ξ_mul_η p k)
  rw [← map_natCast (algebraMap k (edgeRingCharP p k)), CharP.cast_eq_zero, map_zero]

end EdgeFamily
end CerednikDrinfeld

end


