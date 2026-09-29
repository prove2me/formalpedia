-- Prove2me | Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
-- name    : AutomorphicForm_SatakeCombinationCoeff
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/f744f042-a136-5d06-85e2-fce06a6a3cfa
-- title:
--   Satake combination coefficients for base-changed Hecke words
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, and `ws` is a choice, for every height-one prime $v$ of $\mathcal{O}_K$, of an element of `v.Extension (𝓞 L)`, i.e. of a height-one prime of $\mathcal{O}_L$ lying under which $v$ sits.
--
--   The basic object is `univWord n k j`, the two-variable complex polynomial $\mathrm{satakePow}_{n+1}(X_0,X_1)^k\cdot (X_1^{\,n+1})^j$, where `satakePow` is the recursion $p_0 = 2$, $p_1 = s$, $p_{m+2} = s\,p_{m+1} - e\,p_m$; thus $X_0$ plays the role of the sum and $X_1$ of the product of the two Satake parameters, and $p_{n+1}$ is the corresponding power sum. Two sample computations record that for $n = 0$ the words $p_1$ and $X_1$ have coefficient $1$ at the monomials $X_0$ and $X_1$ respectively.
--
--   For a prime $v$ of $\mathcal{O}_K$, `slotDeg` is the inertia degree `inertiaDeg'` of the chosen prime `(ws v).1` over $v$, and `slotWord v kv jv` is `univWord (slotDeg v - 1) kv jv` (truncated subtraction, so the power-sum index is $\mathrm{slotDeg}(v)$ whenever that degree is positive). Given a monomial exponent vector $r \in (\mathrm{Fin}\,2 \to_0 \mathbb{N})$, `slotCoeff v kv jv r` is the coefficient of $r$ in that word, multiplied by $\mathrm{N}(v)^{r(1)}$ and divided by $\mathrm{N}((ws\,v).1)^{jv}$, the renormalisation passing from determinant elements to scalar elements.
--
--   Finally, for exponent functions $k, j$ on primes and a finite set $T$ of primes of $\mathcal{O}_K$ (with decidable equality on primes), `slotIndex` is the `Finset.pi` of the supports of the slot words, i.e. the finite set of dependent functions choosing for each $v \in T$ a monomial occurring in the slot word at $v$; and `slotFamilyCoeff T m` is the product over $v \in T$ of the corresponding `slotCoeff`. These are the index set and the coefficients of the finite linear combination of words at places of $K$ against which a word at the chosen places of $L$ is compared.
--
--   **Relation to Mathlib.** Mathlib has no notion of Satake words or of these combination coefficients; they are the project's own, built on Mathlib's `MvPolynomial`, `Ideal.absNorm` and `Ideal.inertiaDeg'`, on the project's power-sum recursion `satakePow`, and on the project's [`IsDedekindDomain.HeightOneSpectrum.Extension`](../def/DedekindDomain_IntegralClosure.html#L20).
--
--   **Where it is used.** These coefficients serve the base-change and descent bookkeeping for Hecke eigensystems: at a prime $w$ of $L$ above $v$ with inertia degree $f$, a word $T_w^k d_w^j$ is expressed through the power sum $p_f$ in the Hecke eigenvalue and determinant eigenvalue at $v$, and the definitions here package the resulting polynomial coefficients, place by place and over finite sets of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SatakeCombinationCoeff.lean

import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_DedekindDomain_IntegralClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm.SatakeCombination

open MvPolynomial in

def univWord (n k j : ℕ) : MvPolynomial (Fin 2) ℂ :=
  satakePow (n + 1) (X 0) (X 1) ^ k * ((X 1) ^ (n + 1)) ^ j

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))

def slotDeg (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  v.asIdeal.inertiaDeg' (ws v).1.asIdeal

def slotWord (v : HeightOneSpectrum (𝓞 K)) (kv jv : ℕ) : MvPolynomial (Fin 2) ℂ :=
  univWord (slotDeg K L ws v - 1) kv jv

def slotCoeff (v : HeightOneSpectrum (𝓞 K)) (kv jv : ℕ) (r : Fin 2 →₀ ℕ) : ℂ :=
  (slotWord K L ws v kv jv).coeff r * (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) /
    (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ jv

variable (k j : HeightOneSpectrum (𝓞 K) → ℕ)

def slotIndex [DecidableEq (HeightOneSpectrum (𝓞 K))] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset ((v : HeightOneSpectrum (𝓞 K)) → v ∈ T → (Fin 2 →₀ ℕ)) :=
  T.pi fun v => (slotWord K L ws v (k v) (j v)).support

def slotFamilyCoeff (T : Finset (HeightOneSpectrum (𝓞 K)))
    (m : (v : HeightOneSpectrum (𝓞 K)) → v ∈ T → (Fin 2 →₀ ℕ)) : ℂ :=
  ∏ v ∈ T.attach, slotCoeff K L ws v.1 (k v.1) (j v.1) (m v.1 v.2)

end AutomorphicForm.SatakeCombination

example : (AutomorphicForm.SatakeCombination.univWord 0 1 0).coeff (Finsupp.single 0 1) = 1 := by
  simp [AutomorphicForm.SatakeCombination.univWord, AutomorphicForm.satakePow, MvPolynomial.coeff_X']

example : (AutomorphicForm.SatakeCombination.univWord 0 0 1).coeff (Finsupp.single 1 1) = 1 := by
  simp [AutomorphicForm.SatakeCombination.univWord, AutomorphicForm.satakePow, MvPolynomial.coeff_X']

end


