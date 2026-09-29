-- Prove2me | Definitions.Def_KServer_lazy_potential
-- name    : KServer_lazy_potential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-31T15:38:49.023076+00:00
-- url     : https://prove2.me/theorems/f861111d-271a-4d93-a566-fa34591abd87
-- title:
--   The lazy potential for three servers, and the shadow of a work function
-- statement:
--   This file introduces the potential functions of Bein, Chrobak and Larmore's analysis of the $3$-server problem, together with the *shadow* of a work function on which they are all built.
--
--   ## The shadow
--
--   For a work function $w$ and a point $x$, the **shadow** is
--   $$\hat w(x) \;=\; \sup_A\Bigl(\sum_{a \in A} d(x,a) \;-\; w(A)\Bigr),$$
--   the supremum over all configurations $A$; a configuration attaining it is an $(w,x)$-**maximizer**. The shadow is the quantity dual to the work function that controls the pseudo-cost: by the duality property (`KServer.workFnU_duality`, which is Lemma 1 of the paper, due to Koutsoupias–Papadimitriou), an $(w,x)$-maximizer is also an $(w\wedge x, x)$-maximizer *and* maximizes the increase $w\wedge x(A) - w(A)$ caused by a request at $x$. Consequently
--   $$\widehat{w \wedge s}(s) \;+\; r_s(w) \;=\; \hat w(s),$$
--   where $r_s(w) = \max_X\bigl(w\wedge s(X) - w(X)\bigr)$ is the pseudo-cost of the request $s$ — the identity that makes the update property of the potential work.
--
--   The supremum is finite. The work function grows at unit rate away from the initial configuration: taking the base point to be $x$ itself, $w(A) \ge \sum_i d(x, A_i) - \sum_i d(x, C_0(i))$, so
--   $$\hat w(x) \;\le\; \sum_i d\bigl(x, C_0(i)\bigr),$$
--   a bound depending only on $x$ and the initial configuration. No compactness or boundedness of the metric space is needed.
--
--   ## The three-server potentials
--
--   Specialising to $k = 3$ and writing $w(x,y,z)$ for the work function at the configuration $\{x,y,z\}$, the file defines
--
--   $$\tilde w(x,y) \;=\; \sup_{a,a'}\bigl(ya + ya' - w(x,a,a')\bigr),$$
--
--   the shadow restricted to configurations whose first server sits at $x$, and then
--
--   $$\dot w(x) \;=\; \sup_{p,d,d'}\bigl(\tilde w(x,p) + dd' - w(x,p,d) - w(x,p,d')\bigr),$$
--   $$\Psi_{w,r} \;=\; \hat w(r) + \dot w(r).$$
--
--   $\Psi$ is the **lazy potential**. It is obtained by assuming that the adversary is *lazy* — that after the request $r$ it will keep requesting points of its own configuration until the work function becomes a cone — and adding the pseudo-cost accumulated on such a sequence to the potential of the resulting cone. That derivation is only motivation: nothing below depends on it, and only the offset and update properties are ever used.
--
--   Two further potentials are needed because $\Psi$ alone does not satisfy the update property on an arbitrary metric space:
--
--   $$\Lambda_{w,x} = \sup_{p,q,e,e'}\bigl(-xp + \tilde w(x,p) - xq + \tilde w(x,q) - w(x,p,q) + ee' - w(x,e,e')\bigr),$$
--   $$\Gamma_{w,x} = \sup_{p,q,d,d',f}\bigl(-xp + \tilde w(x,p) + xq + dd' - w(x,q,d) - w(x,q,d') + qf - w(x,p,f)\bigr),$$
--
--   and the **semi-lazy potential**
--   $$\hat\Psi_{w,x} \;=\; \max\{\Psi_{w,x},\ \Lambda_{w,x},\ \Gamma_{w,x}\},$$
--
--   which is the value obtained by allowing the adversary to request points outside its own configuration. The technical heart of the paper is that $\Psi_{w,s} \le \hat\Psi_{w,r}$ for every $s$, whence $\hat\Psi$ satisfies the update property; and the Manhattan plane is a metric space on which $\Lambda$ and $\Gamma$ never exceed $\Psi$, so that $\hat\Psi = \Psi$ there and $\Psi$ itself is a $3$-potential.
--
--   **Formalization note.** Configurations are labelled maps `Fin 3 → M` written with Mathlib's `![·,·,·]`, and `workFnU` is invariant under relabelling, so each expression depends only on the underlying multiset. The suprema are `sSup` over ranges; each is bounded above by the unit-rate growth bound above, so none of them is the junk value that `sSup` assigns to an unbounded set. No point is assumed distinct from any other.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354: Section 2 equation (1) (the shadow, and (w,x)-maximizers) and Section 3 (the lazy potential Psi = shadow + dotW, the auxiliary potentials Lambda and Gamma, and the semi-lazy potential Psi-hat = max of the three).

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

/-- The **shadow** of a work function at a point `x`:
`ŵ(x) = sup_A ( Σ_{a ∈ A} d(x,a) − w(A) )`, the supremum over all configurations.

This is the quantity dual to the work function that governs the pseudo-cost: a
configuration attaining the supremum is an `(w, x)`-maximizer, and by the duality property
such a configuration also maximizes the increase of the work function caused by a request
at `x`. The supremum is finite: applying the unit-rate growth of the work function with
base point `x` gives `w(A) ≥ Σ_i d(x, A i) − Σ_i d(x, C₀ i)`, so the shadow is bounded
above by `Σ_i d(x, C₀ i)`. -/
noncomputable def shadow {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (x : M) : ℝ :=
  sSup (Set.range fun A : Config k M => (∑ i, dist x (A i)) - workFnU C₀ σ A)

section Three

variable {M : Type*} [MetricSpace M]

/-- The two-point shadow `w̃(x,y) = sup_{a,a'} ( ya + ya' − w(x,a,a') )`, the shadow taken
over the configurations whose first server sits at `x`. -/
noncomputable def shadow₂ (C₀ : Config 3 M) (σ : List M) (x y : M) : ℝ :=
  sSup (Set.range fun p : M × M =>
    dist y p.1 + dist y p.2 - workFnU C₀ σ ![x, p.1, p.2])

/-- `ẇ(x) = sup_{p,d,d'} ( w̃(x,p) + dd' − w(x,p,d) − w(x,p,d') )`. -/
noncomputable def dotW (C₀ : Config 3 M) (σ : List M) (x : M) : ℝ :=
  sSup (Set.range fun t : M × M × M =>
    shadow₂ C₀ σ x t.1 + dist t.2.1 t.2.2
      - workFnU C₀ σ ![x, t.1, t.2.1] - workFnU C₀ σ ![x, t.1, t.2.2])

/-- The **lazy potential** `Ψ_{w,r} = ŵ(r) + ẇ(r)`.

It is the value of the pseudo-cost accumulated by an adversary that is *lazy* — that keeps
requesting points of its own configuration until the work function becomes a cone — plus
the potential of the resulting cone. Bein, Chrobak and Larmore derive it in this way but
never use that derivation: only the offset and update properties are needed. -/
noncomputable def lazyPot (C₀ : Config 3 M) (σ : List M) (r : M) : ℝ :=
  shadow C₀ σ r + dotW C₀ σ r

/-- The first auxiliary potential
`Λ_{w,x} = sup_{p,q,e,e'} ( −xp + w̃(x,p) − xq + w̃(x,q) − w(x,p,q) + ee' − w(x,e,e') )`. -/
noncomputable def lamPot (C₀ : Config 3 M) (σ : List M) (x : M) : ℝ :=
  sSup (Set.range fun t : M × M × M × M =>
    -dist x t.1 + shadow₂ C₀ σ x t.1 - dist x t.2.1 + shadow₂ C₀ σ x t.2.1
      - workFnU C₀ σ ![x, t.1, t.2.1]
      + dist t.2.2.1 t.2.2.2 - workFnU C₀ σ ![x, t.2.2.1, t.2.2.2])

/-- The second auxiliary potential
`Γ_{w,x} = sup_{p,q,d,d',f} ( −xp + w̃(x,p) + xq + dd' − w(x,q,d) − w(x,q,d') + qf
− w(x,p,f) )`. -/
noncomputable def gamPot (C₀ : Config 3 M) (σ : List M) (x : M) : ℝ :=
  sSup (Set.range fun t : M × M × M × M × M =>
    -dist x t.1 + shadow₂ C₀ σ x t.1 + dist x t.2.1
      + dist t.2.2.1 t.2.2.2.1
      - workFnU C₀ σ ![x, t.2.1, t.2.2.1] - workFnU C₀ σ ![x, t.2.1, t.2.2.2.1]
      + dist t.2.1 t.2.2.2.2 - workFnU C₀ σ ![x, t.1, t.2.2.2.2])

/-- The **semi-lazy potential** `Ψ̂ = max { Ψ, Λ, Γ }`, the potential that actually
satisfies the update property on an arbitrary metric space. The Manhattan plane is a space
on which `Λ` and `Γ` never exceed `Ψ`, so that `Ψ̂ = Ψ` there. -/
noncomputable def semiLazyPot (C₀ : Config 3 M) (σ : List M) (x : M) : ℝ :=
  max (lazyPot C₀ σ x) (max (lamPot C₀ σ x) (gamPot C₀ σ x))

end Three

end KServer


