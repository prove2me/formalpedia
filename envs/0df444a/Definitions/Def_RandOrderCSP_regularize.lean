-- Prove2me | Definitions.Def_RandOrderCSP_regularize
-- name    : RandOrderCSP_regularize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:09:08.8907+00:00
-- url     : https://prove2.me/theorems/fdcc4e12-b2b2-4518-acc7-a9aebd50d744
-- title:
--   Regularization: $H_\Pi$, $\mathrm{Regular}_D$ and $\text{Red-Nbhd-Type}_{D,R}$
-- statement:
--   A **cloud permutation family** for $(H,D)$ is $\Pi=(\pi_{v,b})$ with $\pi_{v,b}$ a permutation of $\mathcal E_H(v)$. It yields a $D$-regular hypergraph $H_\Pi$ with vertices $\{(v,i):i\in\mathcal E_H(v)\}$, edges $\mathcal E_H\times[D]$, and $M_{H_\Pi}((j,b),\ell)=(v,\pi_{v,b}(j))$ for $v=M_H(j,\ell)$, each edge keeping the color of $j$.
--
--   $\mathrm{Regular}_D(\Phi)$ takes $\Pi$ uniform. $\text{Red-Nbhd-Type}_{D,R}(\Phi)$ samples $\Phi'\sim\mathrm{Regular}_D(\Phi)$ and a uniform edge $j$ of $\Phi'$, and returns $\mathrm{type}_R(H',f',j)$. The module defines the average under $\mathrm{Regular}_D$, the expectation of a function under $\text{Red-Nbhd-Type}$, and the mass of a class.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §10.1, pp.49, 51

import Mathlib
import Definitions.Def_RandOrderCSP_typeR
import Definitions.Def_RandOrderCSP_CSP

namespace RandOrderCSP

variable {k : ℕ} {V E C : Type}

/-- The cloud of `v`: the edges `ℰ_H(v)` incident to `v` (§10.1, p.49). -/
abbrev Cloud (H : Hypergraph k V E) (v : V) : Type := {j : E // ∃ ℓ, H.M j ℓ = v}

/-- A cloud permutation family for `(H, D)` (p.49): `Π = (π_{v,b} ∈ Bij(ℰ_H(v)))_{v, b ∈ [D]}`. -/
abbrev CloudFamily (H : Hypergraph k V E) (D : ℕ) : Type :=
  (v : V) → Fin D → Equiv.Perm (Cloud H v)

noncomputable instance [Finite V] [Finite E] (H : Hypergraph k V E) (D : ℕ) :
    Fintype (CloudFamily H D) :=
  Fintype.ofFinite _

/-- **The regularization `H_Π`** (§10.1, p.49).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.49: "ℰ_{H_Π} = ℰ_H × [D], 𝒱_{H_Π} = VE_H,
M_{H_Π}((j, b), ℓ) = (v, π_{v,b}(j)) (j ∈ ℰ_H, b ∈ [D], ℓ ∈ [k], v = M_H(j, ℓ))", and `f_Π(j,b) = f(j)`.

**Formalization Note.** The incidence set `VE_H = {(v,i) : i ∈ ℰ_H(v)}` is the sigma type
`Σ v, Cloud H v`. -/
def regularize (H : Hypergraph k V E) {D : ℕ} (P : CloudFamily H D) :
    Hypergraph k (Σ v, Cloud H v) (E × Fin D) where
  M := fun p ℓ => ⟨H.M p.1 ℓ, P (H.M p.1 ℓ) p.2 ⟨p.1, ℓ, rfl⟩⟩
  row_inj := fun p _ _ h => H.row_inj p.1 (congrArg Sigma.fst h)

/-- `Φ_Π = (H_Π, f_Π)` for a CSP instance `Φ` (p.49). -/
def CSP.regularize {Sig : Type} (Φ : CSP k Sig V E) {D : ℕ} (P : CloudFamily Φ.H D) :
    CSP k Sig (Σ v, Cloud Φ.H v) (E × Fin D) where
  H := RandOrderCSP.regularize Φ.H P
  f := fun p => Φ.f p.1

/-- `E_{Φ′∼Regular_D(Φ)} g(Π)`: the uniform average over cloud permutation families (p.49). -/
noncomputable def regularAvg [Finite V] [Finite E] (H : Hypergraph k V E) (D : ℕ)
    (g : CloudFamily H D → ℝ) : ℝ :=
  (1 / (Fintype.card (CloudFamily H D) : ℝ)) * ∑ P, g P

/-- `E_{N∼Red-Nbhd-Type_{D,R}(Φ)}[v(N)]` (p.51): sample `Φ′ ∼ Regular_D(Φ)`, then a uniformly random
edge `j` of `Φ′`, and evaluate `v` at `type_R(H′, f′, j)`. -/
noncomputable def redNbhdExpect [Finite V] [Fintype E] (H : Hypergraph k V E) (f : E → C) (D R : ℕ)
    (v : RootedClass k C → ℝ) : ℝ :=
  regularAvg H D fun P =>
    (1 / (Fintype.card (E × Fin D) : ℝ)) *
      ∑ p : E × Fin D, v (typeR (regularize H P) (fun p => f p.1) p R)

/-- The probability mass of the class `N` under `Red-Nbhd-Type_{D,R}(Φ)` (p.51). -/
noncomputable def redNbhdLaw [Finite V] [Fintype E] (H : Hypergraph k V E) (f : E → C) (D R : ℕ)
    (N : RootedClass k C) : ℝ := by
  classical
  exact redNbhdExpect H f D R fun N' => if N' = N then 1 else 0

end RandOrderCSP


