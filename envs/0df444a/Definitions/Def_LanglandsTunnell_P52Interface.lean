-- Prove2me | Definitions.Def_LanglandsTunnell_P52Interface
-- name    : LanglandsTunnell_P52Interface
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/38a3e7fb-389a-5114-b7b5-f792610fddea
-- title:
--   The χ−3​ twist weight and a base-change comparison predicate
-- statement:
--   This module fixes two items used in the Langlands–Tunnell part of the tree, both phrased in the project's formal language of Hecke eigensystems. Recall that a `HeckeEigensystem F R` is a structure consisting of a nonzero level ideal of $\mathcal{O}_F$ together with two functions $a,b$ from the height-one spectrum of $\mathcal{O}_F$ to $R$ (formal Satake data at each finite place, with no automorphy built in); `twist` by a function $\chi$ on places sends $a_v\mapsto \chi(v)a_v$, $b_v\mapsto \chi(v)^2 b_v$; `AgreesAwayFromFinite` asserts the existence of a finite set of places outside which both $a$ and $b$ coincide; and `formalBaseChange ℚ K` produces from $\pi$ over $\mathbb{Q}$ the eigensystem over $K$ of level $\top$ whose value at $\mathfrak{P}$ is obtained from the value of $\pi$ at the place below by the Satake recursion $s_0=2$, $s_1=s$, $s_{n+2}=s\,s_{n+1}-e\,s_n$ and by $b\mapsto b^{f}$, the exponent $f$ being the residue degree $\mathfrak{P}/\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$.
--
--   First, `chiNegThreeWeight` is the place-indexed weight over $\mathbb{Q}$ valued in $\mathbb{Z}[\sqrt{-2}]$: a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ is decoded to its rational prime $p$ and sent to $\chi_{-3}(p)\in\{1,-1,0\}$, where $\chi_{-3}(n)$ is $1$, $-1$ or $0$ according as $n\equiv 1,2,0 \pmod 3$, the integer then being cast into $\mathbb{Z}[\sqrt{-2}]$. No identification with an idele-class or Dirichlet-character avatar is asserted.
--
--   Second, `P52InterfaceRow K Φ ΦK`, for a number field $K$ with $\mathcal{O}_K$ integral over $\mathcal{O}_{\mathbb{Q}}$ and eigensystems $\Phi$ over $\mathbb{Q}$ and $\Phi_K$ over $K$ with data in $\mathbb{Z}[\sqrt{-2}]$, says: there is an index $i\in\{0,1\}$ such that the formal base change to $K$ of $\Phi$ (for $i=0$) or of $\Phi\otimes\chi_{-3}$ (for $i=1$) agrees with $\Phi_K$ away from a finite set of places. The selector lies outside the quantifier over places, and nothing is claimed about its uniqueness, about cuspidality, or about attachment to a Galois representation. The lemma `p52InterfaceRow_self` records the degenerate instance: $\Phi_K=\operatorname{formalBaseChange}_{\mathbb{Q}}^{K}\Phi$ satisfies the predicate with $i=0$ and empty exceptional set.
--
--   **Relation to Mathlib.** Mathlib has no notion of Hecke eigensystem, of formal base change of Satake parameters, or of these comparison predicates; they are the project's own. The character $\chi_{-3}$ is likewise defined directly by a residue condition modulo $3$ rather than through Mathlib's Dirichlet characters; only the Dedekind-domain height-one spectrum, residue degrees and $\mathbb{Z}[\sqrt{-2}]=\,$`Zsqrtd (-2)` come from Mathlib.
--
--   **Where it is used.** The predicate packages the shape of statement needed when comparing a weight-one eigensystem over $\mathbb{Q}$ with an eigensystem over an auxiliary field $K$ up to the twist by $\chi_{-3}$, as occurs in the Langlands–Tunnell input to the modularity argument; consumers of the interface supply the selection of the correct member of the two-element family and any uniqueness statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_P52Interface.lean

import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField AutomorphicForm IsDedekindDomain

noncomputable def chiNegThreeWeight : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → ℤ√(-2) :=
  fun v =>
    ((EisensteinWeightOne.chiNegThree
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) v : ℕ) : ℤ) : ℤ√(-2))

def P52InterfaceRow (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) (ΦK : HeckeEigensystem K (ℤ√(-2))) : Prop :=
  ∃ i : Fin 2,
    HeckeEigensystem.AgreesAwayFromFinite
      (formalBaseChange ℚ K (if i = 0 then Φ else Φ.twist chiNegThreeWeight)) ΦK

theorem p52InterfaceRow_self (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) :
    P52InterfaceRow K Φ (formalBaseChange ℚ K Φ) :=
  ⟨0, ∅, fun _ _ => by simp⟩

end LanglandsTunnell


