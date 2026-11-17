-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_QuotCohVanishes
-- name    : GroupIsoPoly_Supplement_QuotCohVanishes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:28:01.141385+00:00
-- url     : https://prove2.me/theorems/988b592c-f5fb-4879-ad3e-a0147a74227b
-- title:
--   No fixed vectors and no first cohomology on $T/J(T)$, with multiplicities and central images
-- statement:
--   For $D$ acting on $T=T_1\otimes T_2\otimes T_3$ over a field $F$, with pairing submodule $J=J(T)$, the property asserts, for every multiplicity $m\ge0$ (the module $(T/J)\otimes_F F^m$):
--
--   1. $\big((T/J)^{m}\big)^D=0$;
--   2. every 1-cocycle $c:D\to(T/J)^m$, $c(gh)=c(g)+g\,c(h)$, is a coboundary $c(g)=(g-1)b$; and for every generating set $S$ of $D$, $b$ is the unique solution of the linear equations $(s-1)b=c(s)$, $s\in S$;
--   3. for every surjective homomorphism $\varphi:D\to\bar D$ with $\ker\varphi\le Z(D)$ such that $\ker\varphi$ acts trivially on $T/J$ (a **central-product image** acting on $T/J$), every 1-cocycle $\bar D\to(T/J)^m$ is a coboundary.
--
--   This packages the conclusions of Theorem 6.3 so that they can be asserted over the defining field and after prime-field descent.
--
--   **Formalization Note** Elements of $T/J$ are written by representatives in $T$ and all identities are congruences modulo $J$; a map to the quotient always lifts. The fixed vectors of $\bar D$ on $T/J$ coincide with those of $D$ because $\varphi$ is onto.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 6.3, p.49 (PDF p.53)

import Mathlib
import Definitions.Def_GroupIsoPoly_Supplement_pairingSubmodule

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

/-- **No fixed vectors and no first cohomology on `T/J(T)`, with multiplicities, generator equations
and central-product images.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 6.3, p.49 (PDF p.53): "(T/J(T))^D = 0,
H1(D, T/J(T)) = 0. The assertions hold after prime-field descent, with fixed multiplicities, and for
a central-product image given with its quotient map. Consequently a cocycle c : D → T/J(T) specified
by its values on the generators has a unique b ∈ T/J(T) with c(g) = (g − 1)b, computable by solving
these linear equations on generators."

Write `T = F^{ι₁} ⊗ F^{ι₂} ⊗ F^{ι₃}` with `D` acting by `g·t = tensorAct ρ₁ ρ₂ ρ₃ g t` and
`J = J(T)`. For every multiplicity `m` (the module `(T/J(T)) ⊗_F F^m`, i.e. `m` copies, a vector being
a family `x : Fin m → T` read modulo `J` in each coordinate) the predicate asserts:
1. **no fixed vectors**: if `g·x_l − x_l ∈ J` for all `g`, `l`, then every `x_l ∈ J`;
2. **`H¹ = 0` and the generator equations**: for every 1-cocycle `c : D → (T/J)^m`, i.e.
   `c(gh) ≡ c(g) + g·c(h) (mod J)`, there is `b` with `c(g) ≡ g·b − b (mod J)` for all `g`; and for every
   generating set `S` of `D`, every `b'` with `c(s) ≡ s·b' − b' (mod J)` for all `s ∈ S` equals `b`
   modulo `J` (so `b` is unique and is the unique solution of the linear equations on generators);
3. **central-product images**: for every surjective homomorphism `φ : D → D̄` with `ker φ ≤ Z(D)`
   through which the action on `T/J` factors (every `g ∈ ker φ` acts trivially on `T/J`), every
   1-cocycle of `D̄` on `(T/J)^m` is a coboundary. (`D̄` acts on `T/J` by `φ(g)·[t] = [g·t]`.)

**Formalization Note.** Elements of `T/J` are written by representatives in `T`; a function to the
quotient always lifts, so cocycles and coboundaries are stated as congruences modulo `J`. The fixed
vectors of `D̄` on `T/J` are those of `D` (`φ` is onto), so clause 1 also covers `D̄`. -/
def QuotCohVanishes {F : Type} [Field F] {D : Type} [Group D]
    {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (ρ₁ : D → Matrix ι₁ ι₁ F) (ρ₂ : D → Matrix ι₂ ι₂ F) (ρ₃ : D → Matrix ι₃ ι₃ F) : Prop :=
  ∀ m : ℕ,
    (∀ x : Fin m → ι₁ × ι₂ × ι₃ → F,
      (∀ g l, tensorAct ρ₁ ρ₂ ρ₃ g (x l) - x l ∈ pairingSubmodule ρ₁ ρ₂ ρ₃) →
        ∀ l, x l ∈ pairingSubmodule ρ₁ ρ₂ ρ₃) ∧
    (∀ c : D → Fin m → ι₁ × ι₂ × ι₃ → F,
      (∀ g h l, c (g * h) l - c g l - tensorAct ρ₁ ρ₂ ρ₃ g (c h l) ∈ pairingSubmodule ρ₁ ρ₂ ρ₃) →
      ∃ b : Fin m → ι₁ × ι₂ × ι₃ → F,
        (∀ g l, c g l - (tensorAct ρ₁ ρ₂ ρ₃ g (b l) - b l) ∈ pairingSubmodule ρ₁ ρ₂ ρ₃) ∧
        ∀ S : Set D, Subgroup.closure S = ⊤ →
          ∀ b' : Fin m → ι₁ × ι₂ × ι₃ → F,
            (∀ s ∈ S, ∀ l, c s l - (tensorAct ρ₁ ρ₂ ρ₃ s (b' l) - b' l) ∈
              pairingSubmodule ρ₁ ρ₂ ρ₃) →
            ∀ l, b' l - b l ∈ pairingSubmodule ρ₁ ρ₂ ρ₃) ∧
    (∀ (Dbar : Type) [Group Dbar] (φ : D →* Dbar), Function.Surjective φ →
      φ.ker ≤ Subgroup.center D →
      (∀ g ∈ φ.ker, ∀ t, tensorAct ρ₁ ρ₂ ρ₃ g t - t ∈ pairingSubmodule ρ₁ ρ₂ ρ₃) →
      ∀ c : Dbar → Fin m → ι₁ × ι₂ × ι₃ → F,
        (∀ g h l, c (φ g * φ h) l - c (φ g) l - tensorAct ρ₁ ρ₂ ρ₃ g (c (φ h) l) ∈
          pairingSubmodule ρ₁ ρ₂ ρ₃) →
        ∃ b : Fin m → ι₁ × ι₂ × ι₃ → F,
          ∀ g l, c (φ g) l - (tensorAct ρ₁ ρ₂ ρ₃ g (b l) - b l) ∈ pairingSubmodule ρ₁ ρ₂ ρ₃)

end Supplement

end GroupIsoPoly


