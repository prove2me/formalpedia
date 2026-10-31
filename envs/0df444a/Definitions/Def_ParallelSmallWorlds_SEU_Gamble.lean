-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_Gamble
-- name    : ParallelSmallWorlds_SEU_Gamble
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:38.703935+00:00
-- url     : https://prove2.me/theorems/cc14441b-e8d3-4e64-b735-410c990068b5
-- title:
--   Compound gambles and the objects $C\cup\mathcal P_S$ compared by $\succeq_{S_w}$
-- statement:
--   A **compound gamble** $\langle\pi_1,b_1;\dots;\pi_r,b_r\rangle$ is a simple distribution over **prizes**, where each prize $b_i$ is either a consequence $c\in C$ or a simple distribution $p\in\mathcal P_S$ over consequences. The relation $\succeq_{S_w}$ compares **objects**: consequences and gambles. Attached to these are:
--
--   1. the embedding of a simple distribution $p$ over $C$ as the gamble whose prizes are its consequences, and the corresponding object;
--   2. the object of a prize ($c$ itself, or the gamble of $p$);
--   3. the distribution over $C$ that a prize leads to ($\Psi_c$ for a consequence $c$, $p$ for a simple distribution $p$);
--   4. the **reduction** of a gamble $g$, the distribution $\rho(c)=\sum_b g(b)\,\mathrm{dist}(b)(c)$, which for $g=\langle\pi_1,p_1;\dots;\pi_s,p_s\rangle$ is $\rho_j=\sum_i\pi_i\pi_{ij}$ (Axiom PSW15);
--   5. **substitution**: the gamble obtained from $g$ by substituting the prize $b'$ for the prize $b$, which moves the probability of $b$ to $b'$ (Axiom PSW14).
--
--   **Formalization Note** Compound gambles are one level deep: prizes are consequences or simple distributions over consequences, which is all that Axioms PSW14, PSW15 and the proof of Lemma 2 use. A consequence $c$ and its degenerate gamble $\Psi_c$ are distinct objects, as in the paper's set $C\cup\mathcal P_S$.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), pp.25–26 (PDF pp.26–27), compound gambles before Axiom PSW14, Axioms PSW14 and PSW15

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_SimpleDist

namespace ParallelSmallWorlds.SEU

/-- **Compound gambles and the objects compared by `⪰Sw`.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), pp.25–26 (PDF pp.26–27): "Let ⟨π1,b1;…;πr,br⟩ ∈ PSw
be the simple distribution which leads to bi ∈ C ∪ PSw with probability πi … by allowing that an
outcome may lie in PSw, we are introducing compound gambles into the model".

* `Gamble C` — a simple distribution over prizes `C ⊕ SimpleDist C` (a prize is a consequence or
  a simple distribution over consequences);
* `Obj C = C ⊕ Gamble C` — the objects `C ∪ PSw` on which `⪰Sw` is a relation (PSW10(a), p.24);
* `SimpleDist.embed p` — a simple distribution `p` over `C`, seen as the gamble whose prizes are
  the consequences; `simpObj p` is the corresponding object;
* `prizeObj b` — a prize, seen as an object (a consequence as itself, a simple distribution `p`
  as `simpObj p`);
* `prizeDist b` — the distribution over `C` a prize leads to (`Ψc` for a consequence `c`);
* `reduceFun g` — the reduced distribution `ρ` of PSW15, p.26: `ρ(c) = Σ_i π_i · p_i(c)`;
* `substFun g b b'` — the gamble `g` with the prize `b'` substituted for the prize `b`
  (PSW14, p.26): the probability `π` of `b` is moved to `b'`.

**Formalization Note.** Compound gambles are one level deep: prizes are consequences or simple
distributions over consequences (reading R7; this is all Axioms PSW14, PSW15 and the proof of
Lemma 2 use). A consequence `c` (`Sum.inl c : Obj C`) and its degenerate distribution `Ψc`
(`simpObj (SimpleDist.pure c)`) are distinct objects, as in the set `C ∪ PSw` of the paper. -/
abbrev Gamble (C : Type*) : Type _ := SimpleDist (C ⊕ SimpleDist C)

/-- The objects `C ∪ PSw` compared by `⪰Sw`: consequences and gambles. -/
abbrev Obj (C : Type*) : Type _ := C ⊕ Gamble C

namespace SimpleDist

variable {C : Type*}

/-- A simple distribution over `C`, as the gamble whose prizes are consequences. -/
noncomputable def embed (p : SimpleDist C) : Gamble C where
  toFun := Finsupp.embDomain (Function.Embedding.inl) p.toFun
  nonneg b := by
    rcases b with c | q
    · have h := Finsupp.embDomain_apply_self (Function.Embedding.inl (β := SimpleDist C))
        p.toFun c
      simp only [Function.Embedding.inl_apply] at h
      rw [h]
      exact p.nonneg c
    · rw [Finsupp.embDomain_of_notMem_range]
      rintro ⟨c, hc⟩
      simp at hc
  sum_eq_one := by
    rw [Finsupp.sum_embDomain]
    exact p.sum_eq_one

end SimpleDist

variable {C : Type*}

/-- A simple distribution over `C` as an object of `C ∪ PSw`. -/
noncomputable def simpObj (p : SimpleDist C) : Obj C :=
  Sum.inr p.embed

/-- A prize (a consequence or a simple distribution) as an object of `C ∪ PSw`. -/
noncomputable def prizeObj : C ⊕ SimpleDist C → Obj C
  | Sum.inl c => Sum.inl c
  | Sum.inr p => simpObj p

/-- The distribution over consequences a prize leads to. -/
noncomputable def prizeDist : C ⊕ SimpleDist C → (C →₀ ℝ)
  | Sum.inl c => Finsupp.single c 1
  | Sum.inr p => p.toFun

/-- The reduction `ρ = Σ_i π_i p_i` of a compound gamble (PSW15, p.26). -/
noncomputable def reduceFun (g : Gamble C) : C →₀ ℝ :=
  g.toFun.sum (fun b r => r • prizeDist b)

/-- The gamble `g` with prize `b'` substituted for prize `b` (PSW14, p.26). -/
noncomputable def substFun (g : Gamble C) (b b' : C ⊕ SimpleDist C) :
    (C ⊕ SimpleDist C) →₀ ℝ :=
  g.toFun.erase b + Finsupp.single b' (g.toFun b)

end ParallelSmallWorlds.SEU


