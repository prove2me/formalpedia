-- Prove2me | Definitions.Def_ModularCurve_AttachmentConcrete
-- name    : ModularCurve_AttachmentConcrete
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/90b165da-b071-5f59-aa44-e2082ced91c8
-- title:
--   Eichler–Shimura local clauses instantiated at the modular Jacobian
-- statement:
--   Two abbreviations specialise the abstract local clauses of the Eichler–Shimura package to the concrete modular Jacobian. The ambient data are natural numbers $N$ and $p$ with $N$ nonzero, together with an assumed `HeckeAlg`-module structure on `JZero N`; here `HeckeAlg` is the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$ on one generator `heckeGen ℓ` per rational prime, and `JZero N` is the degree-zero divisor class group $\mathrm{Pic}^0$ of the intermediate field obtained by base-changing to $\overline{\mathbb{Q}}$ (Mathlib's `AlgebraicClosure ℚ`) the field generated over $\mathbb{Q}$ inside $\mathbb{Q}((q))$ by the $q$-expansions $j(q^d)$ for the divisors $d \mid N$, with the coefficientwise action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on divisor classes.
--
--   `UnramifiedOutsideConcrete N p` is the statement that for every prime $\ell$ not dividing $Np$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $\ell$ and every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, one has $\sigma \cdot x = x$ for every $x \in$ `JZero N` killed by some power of $p$: the $p$-power torsion is unramified away from $Np$.
--
--   `FrobeniusQuadraticConcrete N p` is the Eichler–Shimura congruence in operator form: for every prime $\ell \nmid Np$, every valuation subring $A$ over $\ell$, every $\sigma$ which is a Frobenius at $\ell$ for $A$, and every $p$-power torsion point $x$,
--   $$\sigma^2 x - X_\ell \cdot (\sigma x) + \ell x = 0,$$
--   with $X_\ell$ the Hecke generator at $\ell$. Both are predicates (elements of `Prop`) on the chosen model of the modular function field and on the assumed Hecke action, to be cited as hypotheses rather than proved here; the relation asserted is a congruence holding on $p$-power torsion, not an identity of endomorphisms of the whole Jacobian.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used (`AlgebraicClosure ℚ`, `ValuationSubring`, Laurent series), but has no modular curves, Hecke algebras or modular Jacobians; the Jacobian `JZero`, the Hecke algebra `HeckeAlg` and the local clauses instantiated here are the project's own.
--
--   **Where it is used.** These two predicates package clauses (ii) and (iii) of the Eichler–Shimura input — Néron–Ogg–Shafarevich for $J_0(N)$ and the congruence $\mathrm{Frob}_\ell^2 - T_\ell\,\mathrm{Frob}_\ell + \ell = 0$ — in the form in which they are cited when attaching a two-dimensional mod $p$ Galois representation to a residual Hecke eigensystem, the step matched against the representation coming from the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_AttachmentConcrete.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section ConcreteCitation

variable (N p : ℕ) [NeZero N]
variable [Module HeckeAlg (JZero N)]

abbrev UnramifiedOutsideConcrete : Prop :=
  UnramifiedOutside (K := ℚ) (L := AlgebraicClosure ℚ) N p (JZero N)

abbrev FrobeniusQuadraticConcrete : Prop :=
  FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p (JZero N)

end ConcreteCitation

end ModularCurve

end


