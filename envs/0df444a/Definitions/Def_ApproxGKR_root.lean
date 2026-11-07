-- Prove2me | Definitions.Def_ApproxGKR_root
-- name    : ApproxGKR_root
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:01.120212+00:00
-- url     : https://prove2.me/theorems/55d94251-d723-4593-b083-e142603ea85c
-- title:
--   Roots of unity $\omega_N^a=\exp(2\pi i a/N)$ and the set $\Omega_N$
-- statement:
--   For natural numbers $N$ and $a$, the **root of unity with index $a$** of order $N$ is
--   $$\mathrm{root}_N(a)=\exp(2\pi i a/N),$$
--   and $\Omega_N=\{\exp(2\pi i a/N):0\le a<N\}$ is the set of $N$th roots of unity. The label alphabet of the protocol is $H=\Omega_h$, and the verifier's challenges are drawn from $\Omega_N$.
--
--   Labels and challenges are carried as integer indices: "A uniform integer index specifies an exact root; only its numerical evaluation is approximate" (p.32). Every statement of the mission refers to the exact root specified by an index.
--
--   **Formalization Note** $\Omega_N$ is a finite set of complex numbers (the image of $\{0,\dots,N-1\}$). For $a\ge N$ the formula wraps around.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §2.1, p.5; §C.1, pp.30, 32

import Mathlib

namespace ApproxGKR

/-- The root of unity with index `a` of order `N`, `root N a = exp(2πia/N)`.

A. Das, D. Gupta, A. Mondal, M. More, *Delegating Computation with Approximate Arithmetic:
Interactive Proofs for Wizards*, manuscript (sha256 78b2a36b…), §2.1, p.5 and §C.1, pp.30, 32:
"let `Ω_N = {exp(2πia/N) : 0 ≤ a < N}` be the set of `N`th roots of unity, and define `Ω_h` in the
same way"; "`H = {exp(2πia/h) : 0 ≤ a < h}`"; "A uniform integer index specifies an exact root".

**Formalization Note** Labels and challenges are carried as integer indices `a`; `root N a` is
the exact complex root that the index specifies. For `a ≥ N` the value wraps around. -/
noncomputable def root (N a : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (N : ℂ))

open Classical in
/-- The set `Ω_N = {exp(2πia/N) : 0 ≤ a < N}` of `N`th roots of unity (§2.1, p.5; §C.1,
p.32), as a finite set of complex numbers. `Ω_h = H` is the label alphabet (p.30). -/
noncomputable def Omega (N : ℕ) : Finset ℂ :=
  (Finset.range N).image (root N)

end ApproxGKR


