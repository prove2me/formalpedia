-- Prove2me | Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
-- name    : LanglandsTunnell_Converse_ExplicitWhittakerFunctions
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/79de8eec-4dba-52e7-ab92-d3638b2fa6bd
-- title:
--   Explicit archimedean Whittaker functions: principal and discrete families
-- statement:
--   Two explicit complex-valued functions on $2\times 2$ real matrices are defined, together with their auxiliary ingredients; the module contains no theorem. Throughout, $\psi(x)=\exp(2\pi i x)$ and $\mathrm{quasiChar}\,u\,a\,(y)=|y|^{u}$ times $\operatorname{sign}(y)$ when $a\neq 0$ in $\mathbb{Z}/2$ and times $1$ when $a=0$.
--
--   Principal family. `phiStd a v` is Tate's standard real test function of parity $a$, namely $e^{-\pi v^{2}}$ for $a=0$ and $v\,e^{-\pi v^{2}}$ for $a\neq 0$. For parities $a_1,a_2$, a matrix $h$ and $t\in\mathbb{R}$, `innerW` is the integral over $x\in\mathbb{R}$ of $\phi_{a_1}\bigl(-t(h_{00}+x h_{10})\bigr)\,\phi_{a_2}\bigl(-t(h_{01}+x h_{11})\bigr)\,\psi(-x)$. Then `Wmem u₁ u₂ a₁ a₂ g` is $|\det g|$ times $\mathrm{quasiChar}\,u_1\,a_1(\det g)$ times the integral over $t\in\mathbb{R}$ of `innerW a₁ a₂ g t` against $\mathrm{quasiChar}\,(u_1-u_2)\,(a_1+a_2)(t)$. Both integrals are Bochner integrals, so each is $0$ where its integrand fails to be integrable; no convergence is asserted by the definition.
--
--   Discrete family. For a matrix $g$ with bottom row $(c,d)$: `nsq g` $=c^{2}+d^{2}$, `iy g` $=\det g/\mathrm{nsq}\,g$, `ix g` $=(g_{00}c+g_{01}d)/\mathrm{nsq}\,g$ and `kap g` $=(d-ci)/\sqrt{\mathrm{nsq}\,g}$, these being the Iwasawa coordinates and the rotation phase of $g$; `pexp k₀` $=k_0/2+1$ and `prof k₀ y` $=y^{k_0/2+1}e^{-2\pi y}$ is the radial profile; `detPow u₀ g` $=\exp\bigl(u_0\log\det g\bigr)$. Finally `W u₀ k₀ g` is, for $\det g>0$,
--   $$\psi(\mathrm{ix}\,g)\cdot \mathrm{prof}\,k_0(\mathrm{iy}\,g)\cdot (\mathrm{kap}\,g)^{k_0+1}\cdot\sqrt{\mathrm{nsq}\,g}\cdot \mathrm{detPow}\,u_0\,g,$$
--   and $0$ when $\det g\le 0$.
--
--   **Relation to Mathlib.** Mathlib has no notion of Whittaker function; these are the project's own explicit functions, written with Mathlib's Bochner integral, exponential and square root (so the usual conventions for a non-integrable integrand and for division by zero apply).
--
--   **Where it is used.** These are the candidate Whittaker functions at a real place feeding the converse-theorem machinery for $\mathrm{GL}_2$: they are intended to realise the archimedean data `ArchDatumR` for a principal-series and for a discrete-series real parameter, whose required properties (smoothness on the invertible matrices, the unipotent and central transformation laws, the zeta package with functional equation, and the decay bounds) are established elsewhere. That machinery serves the Langlands–Tunnell step, which supplies the modularity of the odd two-dimensional representation attached to the mod $3$ representation of the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Complex LanglandsTunnell.Converse.ArchR

namespace LanglandsTunnell.Converse

namespace PrincipalFamily

def phiStd (a : ZMod 2) (v : ℝ) : ℂ :=
  (if a = 0 then 1 else (v : ℂ)) * (Real.exp (-Real.pi * v ^ 2) : ℂ)

def innerW (a₁ a₂ : ZMod 2) (h : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, phiStd a₁ (-(t * (h 0 0 + x * h 1 0))) * phiStd a₂ (-(t * (h 0 1 + x * h 1 1))) * psi (-x)

def Wmem (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det * ∫ t : ℝ, innerW a₁ a₂ g t * quasiChar (u₁ - u₂) (a₁ + a₂) t

end PrincipalFamily

namespace DiscreteFamily

def nsq (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := g 1 0 ^ 2 + g 1 1 ^ 2

def iy (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := g.det / nsq g

def ix (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (g 0 0 * g 1 0 + g 0 1 * g 1 1) / nsq g

def kap (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((g 1 1 : ℂ) - (g 1 0 : ℂ) * I) / (Real.sqrt (nsq g) : ℂ)

def pexp (k₀ : ℕ) : ℝ := (k₀ : ℝ) / 2 + 1

def prof (k₀ : ℕ) (y : ℝ) : ℝ := y ^ pexp k₀ * Real.exp (-(2 * Real.pi * y))

def detPow (u₀ : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := Complex.exp (u₀ * (Real.log g.det : ℂ))

def W (u₀ : ℂ) (k₀ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  if 0 < g.det then
    psi (ix g) * (prof k₀ (iy g) : ℂ) * kap g ^ (k₀ + 1) * (Real.sqrt (nsq g) : ℂ) * detPow u₀ g
  else 0

end DiscreteFamily

end LanglandsTunnell.Converse

end


