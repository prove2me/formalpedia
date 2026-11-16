-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
-- name    : GoldreichAffine_Exponential_Supplement_Modular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:47:52.251985+00:00
-- url     : https://prove2.me/theorems/ee32799e-5010-4ac4-819c-063e6df979e5
-- title:
--   Modular predicates MOD$^{t,S_0}_d$, MOD12, signed weight profile, Fourier coefficients, binomial transform and $B_{12}$
-- statement:
--   For integers $t\ge2$ and a residue set $S_0\subseteq[t]=\{0,\dots,t-1\}$, the **modular predicate** on $d$ inputs is
--
--   $$\mathsf{MOD}^{t,S_0}_d(x)=\begin{cases}0,&\|x\|\bmod t\in S_0,\\1,&\text{otherwise,}\end{cases}$$
--
--   where $\|x\|$ is the Hamming weight. $\mathsf{MOD12}_b=\mathsf{MOD}^{12,S_0}_b$ with $S_0=\{0,1,3,4,6,9\}$.
--
--   The **signed weight profile** is $g_{t,S_0}(w)=1$ if $w\bmod t\in S_0$ and $-1$ otherwise, for $w\ge0$. Its **Fourier coefficients** are
--
--   $$\widehat g_\nu=\frac1t\sum_{w=0}^{t-1}g(w)\,\omega^{-\nu w},\qquad\omega=e^{2\pi i/t},\quad0\le\nu<t .$$
--
--   For a binary sequence $a=(a(h))_{h\ge0}$ over $\mathbb F_2$, its **binomial transform** is
--
--   $$\lambda^a_j(w)=\sum_{h=0}^{j}\binom jh a(w+h)\pmod 2,\qquad j,w\ge0 .$$
--
--   For $\mathsf{MOD}^{t,S_0}$ the paper uses $a(h)=(1-g(h))/2$, which is $1$ exactly when $h\bmod t\notin S_0$ (the predicate's value at weight $h$); the resulting $\lambda_j(w)$ is the common coefficient of all degree-$j$ monomials in the algebraic normal form of a residual whose fixed inputs have weight $w$.
--
--   Finally, for $b'\ge1$,
--
--   $$B_{12}(b')=\frac{\sqrt2}{6}\Big[\Big(\cos\frac\pi{12}\Big)^{b'}+\Big(\sin\frac\pi{12}\Big)^{b'}+2^{-b'/2}\Big]+\frac1{\sqrt3}\Big(\frac{\sqrt3}{2}\Big)^{b'} .$$
--
--   These objects state Lemma 5, Theorems 3 and 6, and Lemmas 7–8.
--
--   **Formalization Note** The output bit $0$ is `false` and $1$ is `true`; the paper's polarity ($0$ on $S_0$) is kept. Residue sets are finite sets of naturals; the standing condition $S_0\subseteq[t]$ is a hypothesis of each theorem. $\mathbb F_2$ is `ZMod 2`, and $2^{-b'/2}$ is a real power.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 3 (PDF p. 4) MOD definition; p. 10 (PDF p. 11) MOD12 and Theorem 6 (B12); App. B.1 p. 25 (PDF p. 26) signed profile and Fourier coefficients; App. B.3 p. 30 (PDF p. 31) λ_j(w)

import Definitions.Def_GoldreichAffine_Exponential_BooleanCore
open scoped BigOperators
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- MOD^{t,S0}_d (printed p.3 / PDF p.4): value 0 (false) iff ‖x‖ mod t ∈ S0, else 1 (true). -/
def modPredicate (t : ℕ) (S0 : Finset ℕ) (d : ℕ) : Predicate d :=
  fun x => !decide (weight x % t ∈ S0)

/-- The residue set S0 = {0,1,3,4,6,9} of MOD12 (printed p.10 / PDF p.11). -/
def mod12Residues : Finset ℕ := {0, 1, 3, 4, 6, 9}

/-- MOD12_b = MOD^{12,S0}_b with S0 = {0,1,3,4,6,9}. -/
def mod12 (b : ℕ) : Predicate b := modPredicate 12 mod12Residues b

/-- Signed weight profile g_{t,S0}(w) = 1 if w mod t ∈ S0, -1 otherwise (printed p.25 / PDF p.26). -/
def signedProfile (t : ℕ) (S0 : Finset ℕ) (w : ℕ) : ℤ :=
  if w % t ∈ S0 then 1 else -1

/-- Fourier coefficient ĝ_ν = (1/t) Σ_{w=0}^{t-1} g(w) ω^{-νw}, ω = exp(2πi/t). -/
noncomputable def fourierCoeff (t : ℕ) (S0 : Finset ℕ) (ν : ℕ) : ℂ :=
  (1 / (t : ℂ)) * ∑ w ∈ Finset.range t,
    (signedProfile t S0 w : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (w : ℂ) / (t : ℂ)))

/-- Binomial transform of a binary sequence a over F₂:
    λ^a_j(w) = Σ_{h=0}^{j} C(j,h) a(w+h)  (printed p.30 / PDF p.31). -/
def binomialTransform (a : ℕ → ZMod 2) (j w : ℕ) : ZMod 2 :=
  ∑ h ∈ Finset.range (j + 1), (j.choose h : ZMod 2) * a (w + h)

/-- The binary sequence (1 - g_{t,S0}(h))/2: 1 iff h mod t ∉ S0, i.e. the MOD value at weight h.
    So binomialTransform (modSequence t S0) j w is the paper's λ_j(w). -/
def modSequence (t : ℕ) (S0 : Finset ℕ) (h : ℕ) : ZMod 2 :=
  if h % t ∈ S0 then 0 else 1

/-- The sequence of MOD12: its binomial transform gives λ_j(w) for MOD12_b. -/
def mod12Sequence : ℕ → ZMod 2 := modSequence 12 mod12Residues

/-- B12(b') of Theorem 6 (printed pp.10–11 / PDF pp.11–12), exactly as printed;
    2^{-b'/2} is a real power. -/
noncomputable def B12 (b' : ℕ) : ℝ :=
  Real.sqrt 2 / 6 * (Real.cos (Real.pi / 12) ^ b' + Real.sin (Real.pi / 12) ^ b'
      + (2 : ℝ) ^ (-(b' : ℝ) / 2))
    + 1 / Real.sqrt 3 * (Real.sqrt 3 / 2) ^ b'

end GoldreichAffine.Exponential.Supplement


