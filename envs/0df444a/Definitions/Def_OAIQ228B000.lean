-- Prove2me | Definitions.Def_OAIQ228B000
-- name    : OAIQ228B000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:15:11.602941+00:00
-- url     : https://prove2.me/theorems/5833b0af-319b-4058-b77d-80f7fae4b492
-- title:
--   Definitions bundle OAIQ228B000 of the split of OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 561 declarations of OpenAI's Lean: 430 definitions, 17 inductive types or structures, 10 instances and 104 theorems. The definitions and types are `OAI.ActionOrbitTransport.PairOrbit`, `OAI.ActionOrbitTransport.pairOrbit`, `OAI.ActionOrbitTransport.stabilizerOrbit`, `OAI.ActionOrbitTransport.suborbitCard`, `OAI.CriticalPercolation.AlgebraicDescent`, `OAI.CriticalPercolation.BernoulliProduct.DecisionCode`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.codeOf`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.failure`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.partition`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.partitionWithBlock`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.state`, `OAI.CriticalPercolation.BernoulliProduct.HasFiniteOpenWitness`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition.decide`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition.enlarge`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition.historySigma`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition.probability`, `OAI.CriticalPercolation.BernoulliProduct.allOpen`, `OAI.CriticalPercolation.BernoulliProduct.atParameter`, `OAI.CriticalPercolation.BernoulliProduct.bitMeasure`, `OAI.CriticalPercolation.BernoulliProduct.bitWeight`, `OAI.CriticalPercolation.BernoulliProduct.blockProbability`, `OAI.CriticalPercolation.BernoulliProduct.blockSigma`, `OAI.CriticalPercolation.BernoulliProduct.closedBlock`, `OAI.CriticalPercolation.BernoulliProduct.coordinateSigma`, `OAI.CriticalPercolation.BernoulliProduct.finiteCoordinateEvents`, `OAI.CriticalPercolation.BernoulliProduct.forceOn`, `OAI.CriticalPercolation.BernoulliProduct.law`, `OAI.CriticalPercolation.BernoulliProduct.markLaw`, `OAI.CriticalPercolation.BernoulliProduct.pinnedParameters`, `OAI.CriticalPercolation.BernoulliProduct.predictionFailure`, `OAI.CriticalPercolation.BernoulliProduct.reindexMarks`, `OAI.CriticalPercolation.BernoulliProduct.selectedEvent`, `OAI.CriticalPercolation.BernoulliProduct.twoPredictions`, `OAI.CriticalPercolation.BinaryInterpolation.bisect`, `OAI.CriticalPercolation.BinaryInterpolation.midpoint`, `OAI.CriticalPercolation.BinaryInterpolation.terminal`, `OAI.CriticalPercolation.BinaryLaw.ActiveIndex`, `OAI.CriticalPercolation.BinaryLaw.Canonical` and 407 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `CriticalPercolation_Classification_AlgebraicDescent`, `CriticalPercolation_Classification_FaithfulOrbitalModel`, `CriticalPercolation_Classification_StructuredCoordinates`, `CriticalPercolation_Clusters_ClusterNumber`, `CriticalPercolation_Clusters_ClusterObject`, `CriticalPercolation_Clusters_ClusterTail`, `CriticalPercolation_Clusters_ClusterUpdate`, `CriticalPercolation_Clusters_DeleteBot`, `CriticalPercolation_Clusters_Earlier`, `CriticalPercolation_Clusters_ExpectedCluster`, `CriticalPercolation_Clusters_ForcedDisconnectContinuity`, `CriticalPercolation_Clusters_HitOthers`, `CriticalPercolation_Clusters_HitValue`, `CriticalPercolation_Clusters_InfiniteUniqueness`, `CriticalPercolation_Clusters_InfiniteUniquenessGeometry`, `CriticalPercolation_Criticality_BalancedCycles`, `CriticalPercolation_Criticality_BandScale`, `CriticalPercolation_Criticality_BlockIndependence`, `CriticalPercolation_Criticality_ComponentCritical`, `CriticalPercolation_Criticality_ContractingDomains`, `CriticalPercolation_Criticality_CylinderApproximation`, `CriticalPercolation_Criticality_DescendingFan`, `CriticalPercolation_Criticality_DirectionalTail`, `CriticalPercolation_Criticality_FiniteInterpolation`, `CriticalPercolation_Criticality_FiniteSeedTree`, `CriticalPercolation_Criticality_FiniteSusceptibility`, `CriticalPercolation_Criticality_GrowthAlternatives`, `CriticalPercolation_Criticality_GrowthProcess`, `CriticalPercolation_Criticality_HeightCuts`, `CriticalPercolation_Criticality_InvariantFiniteSets`, `CriticalPercolation_Criticality_LayerCounting`, `CriticalPercolation_Criticality_MainResidualBoundary`, `CriticalPercolation_Criticality_NestedLayerBlock`, `CriticalPercolation_Criticality_OpenRay`, `CriticalPercolation_Criticality_RestrictedSeed`, `CriticalPercolation_Criticality_ReverseReference`, `CriticalPercolation_Criticality_SquareBoundary`, `CriticalPercolation_Criticality_SubexponentialVolumes`, `CriticalPercolation_Criticality_WitnessEvents`, `CriticalPercolation_Entropy_BinaryConfiguration`, `CriticalPercolation_Entropy_BinaryCosts`, `CriticalPercolation_Entropy_BinaryDescriptor`, `CriticalPercolation_Entropy_BinaryEventBound`, `CriticalPercolation_Entropy_BinaryForest`, `CriticalPercolation_Entropy_BinaryInterpolation`, `CriticalPercolation_Entropy_BinaryInverseCost`, `CriticalPercolation_Entropy_BinaryLaw`, `CriticalPercolation_Entropy_BinaryLikelihood`, `CriticalPercolation_Entropy_BinaryMarks`, `CriticalPercolation_Entropy_BinaryOutput`, `CriticalPercolation_Entropy_BinaryOutputEntropy`, `CriticalPercolation_Entropy_BinaryPairs`, `CriticalPercolation_Entropy_BinaryParents`, `CriticalPercolation_Entropy_BinaryRaw`, `CriticalPercolation_Entropy_BinaryReferenceLikelihood`, `CriticalPercolation_Entropy_BinaryReverseKernels`, `CriticalPercolation_Entropy_BinaryReversePrices`, `CriticalPercolation_Entropy_BinaryStages`, `CriticalPercolation_Entropy_BinarySupport`, `CriticalPercolation_Entropy_BinarySwitches`, `CriticalPercolation_Entropy_BinaryTranscript`, `CriticalPercolation_Entropy_BinaryWords`, `CriticalPercolation_Entropy_MarkedBits`, `CriticalPercolation_Entropy_MarkedEntropy`, `CriticalPercolation_Entropy_ReverseGuess`, `CriticalPercolation_Entropy_Uniform01`, `CriticalPercolation_Exploration_AdaptiveReveal`, `CriticalPercolation_Exploration_AncestryForest`, `CriticalPercolation_Exploration_BallIncidence`, `CriticalPercolation_Exploration_BitWeight`, `CriticalPercolation_Exploration_ClosedFresh`, `CriticalPercolation_Exploration_ClosedPivotWeight`, `CriticalPercolation_Exploration_ClusterUsers`, `CriticalPercolation_Exploration_DecisionHistory`, `CriticalPercolation_Exploration_Initial`, `CriticalPercolation_Exploration_Initial2`, `CriticalPercolation_Exploration_LayerExposure`, `CriticalPercolation_Exploration_Node`, `CriticalPercolation_Exploration_OpenFrontierDivergence`, `CriticalPercolation_Exploration_QueryDelta`, `CriticalPercolation_Exploration_QueryTree`, `CriticalPercolation_Exploration_SearchTree`, `CriticalPercolation_Exploration_SequentialExposure`, `CriticalPercolation_Exploration_SliceExploration`, `CriticalPercolation_Exploration_State`, `CriticalPercolation_Gluing_CollarDistance`, `CriticalPercolation_Gluing_ConditionalGluing`, `CriticalPercolation_Gluing_ContactSelection`, `CriticalPercolation_Gluing_ContourSites`, `CriticalPercolation_Gluing_ContourWords`, `CriticalPercolation_Gluing_CorridorNormalization`, `CriticalPercolation_Gluing_CorridorScaleChoice`, `CriticalPercolation_Gluing_CorridorSeparation`, `CriticalPercolation_Gluing_DomainFreshExit`, `CriticalPercolation_Gluing_EllipseMoves`, `CriticalPercolation_Gluing_FreshExitWitness`, `CriticalPercolation_Gluing_FreshTrial`, `CriticalPercolation_Gluing_LevelContactGeometry`, `CriticalPercolation_Gluing_MoveExit`, `CriticalPercolation_Gluing_MoveWitness`, `CriticalPercolation_Gluing_PinnedTest`, `CriticalPercolation_Gluing_RelayGeometry`, `CriticalPercolation_Gluing_RelayMoves`, `CriticalPercolation_Gluing_RelayScales`, `CriticalPercolation_Gluing_SelectedFresh`, `CriticalPercolation_Gluing_SlotContour`, `CriticalPercolation_Gluing_SourceGraph`, `CriticalPercolation_Gluing_StripMoves`, `CriticalPercolation_GraphGeometry_BallCutGeometry`, `CriticalPercolation_GraphGeometry_Column`, `CriticalPercolation_GraphGeometry_ComponentAction`, `CriticalPercolation_GraphGeometry_Connects`, `CriticalPercolation_GraphGeometry_CoordinateScheme`, `CriticalPercolation_GraphGeometry_CutEdges`, `CriticalPercolation_GraphGeometry_DeletedTailGeometry`, `CriticalPercolation_GraphGeometry_EllipseExit`, `CriticalPercolation_GraphGeometry_EllipseLinear`, `CriticalPercolation_GraphGeometry_EllipseMesh`, `CriticalPercolation_GraphGeometry_EllipseSeed`, `CriticalPercolation_GraphGeometry_EncounterGeometry`, `CriticalPercolation_GraphGeometry_EraseBond`, `CriticalPercolation_GraphGeometry_FiniteIndexAction`, `CriticalPercolation_GraphGeometry_FiniteInduced`, `CriticalPercolation_GraphGeometry_FullOrbitalStructureTransfer`, `CriticalPercolation_GraphGeometry_GraphAction`, `CriticalPercolation_GraphGeometry_GraphActionCoordinates`, `CriticalPercolation_GraphGeometry_GraphBalls`, `CriticalPercolation_GraphGeometry_GraphQuotientPolynomial`, `CriticalPercolation_GraphGeometry_HitEvent`, `CriticalPercolation_GraphGeometry_InducedAutomorphism`, `CriticalPercolation_GraphGeometry_IsolateThree`, `CriticalPercolation_GraphGeometry_LatticeGrowth`, `CriticalPercolation_GraphGeometry_MapVertices`, `CriticalPercolation_GraphGeometry_MovingStrips`, `CriticalPercolation_GraphGeometry_ObjectKernel`, `CriticalPercolation_GraphGeometry_OpenGraphIso`, `CriticalPercolation_GraphGeometry_OrbitRepresentatives`, `CriticalPercolation_GraphGeometry_OrbitalAction`, `CriticalPercolation_GraphGeometry_OrbitalPower`, `CriticalPercolation_GraphGeometry_RestrictVertices`, `CriticalPercolation_GraphGeometry_RestrictedAction`, `CriticalPercolation_GraphGeometry_StripCompactness`, `CriticalPercolation_GraphGeometry_StripLinear`, `CriticalPercolation_GraphGeometry_UniformGeometry`, `CriticalPercolation_GraphGeometry_UpdateKernel`, `CriticalPercolation_GraphGeometry_VertexBall`, `CriticalPercolation_GraphGeometry_WiredEvent`, `CriticalPercolation_GraphTopology_OrbitalNeighborhoods`, `CriticalPercolation_Growth_SuperpolynomialRadius`, `CriticalPercolation_LinearGroups_ClusterMatrix`, `CriticalPercolation_Modular_ActionOrbitTransport`, `CriticalPercolation_Modular_CappedDiscrepancy`, `CriticalPercolation_Modular_ClusterDiscrepancy`, `CriticalPercolation_Modular_CriticalHeavyIdentity`, `CriticalPercolation_Modular_DiscrepancyTail`, `CriticalPercolation_Modular_ExpectedIncidenceTransport`, `CriticalPercolation_Modular_GraphModular`, `CriticalPercolation_Modular_HeavyClusterNumber`, `CriticalPercolation_Modular_HeavyFiniteGeometry`, `CriticalPercolation_Modular_HeavyHarris`, `CriticalPercolation_Modular_HeavyPeaks`, `CriticalPercolation_Modular_HeavyThinning`, `CriticalPercolation_Modular_LightClusterNumber`, `CriticalPercolation_Modular_LightSliceFrontier`, `CriticalPercolation_Modular_LightTwoPointDecay`, `CriticalPercolation_Modular_ModularCharacter`, `CriticalPercolation_Modular_ModularClusterCount`, `CriticalPercolation_Modular_ModularClusterMass`, `CriticalPercolation_Modular_ModularIncidence`, `CriticalPercolation_Modular_ModularLevelGeometry`, `CriticalPercolation_Modular_ModularSuperlevels`, `CriticalPercolation_Modular_NormalizedDiscrepancy`, `CriticalPercolation_Modular_NormalizedIncidenceTransport`, `CriticalPercolation_Modular_ObjectAvoidMass`, `CriticalPercolation_Modular_OrbitalMassTransport`, `CriticalPercolation_Modular_PeakClusters`, `CriticalPercolation_Modular_PeakRatioTransport`, `CriticalPercolation_Modular_PeakReturn`, `CriticalPercolation_Modular_PeakVolumeBand`, `CriticalPercolation_Modular_PushMass`, `CriticalPercolation_Modular_RelativeModular`, `CriticalPercolation_Modular_SignedDiscrepancyContinuity`, `CriticalPercolation_Modular_TiltedTransportENNReal`, `CriticalPercolation_Modular_UnimodularGeometric`, `CriticalPercolation_Modular_Unimodularity`, `CriticalPercolation_Modular_WeightedDiscrepancy`, `CriticalPercolation_Modular_WeightedDiscrepancyLimit`, `CriticalPercolation_Modular_WeightedPeakTransport`, `CriticalPercolation_ProductMeasure_BitMeasure`, `CriticalPercolation_ProductMeasure_ContourProbability`, `CriticalPercolation_ProductMeasure_Delta`, `CriticalPercolation_ProductMeasure_Density`, `CriticalPercolation_ProductMeasure_Distribution`, `CriticalPercolation_ProductMeasure_FiniteInterpolationMeasure`, `CriticalPercolation_ProductMeasure_FiniteOpenWitness`, `CriticalPercolation_ProductMeasure_FiniteProductPin`, `CriticalPercolation_ProductMeasure_LayerExpectation`, `CriticalPercolation_ProductMeasure_LevelContactMeasurability`, `CriticalPercolation_ProductMeasure_MonotoneBernoulli`, `CriticalPercolation_ProductMeasure_Prob`, `CriticalPercolation_ProductMeasure_ProductConditioning`, `CriticalPercolation_ProductMeasure_RelayProbability`, `CriticalPercolation_ProductMeasure_TailProduct`.
--
--   **Imports.** It imports the published bundle `Def_CriticalPercolation`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ228B002`; the statements `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.enn_fiber_sum`, `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.incoming_finite_ae`, `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal`, `OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction`, `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae`, `OAI.CriticalPercolation.BondGraph.atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.band_volume_peak`, `OAI.CriticalPercolation.BondGraph.band_volume_ratio`, `OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end`, `OAI.CriticalPercolation.BondGraph.bondWeight_le_of_clusterPeak`, `OAI.CriticalPercolation.BondGraph.bondWeight_ne_top`, `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_le_one`, `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_ne_zero_of_mass_ne_top`, `OAI.CriticalPercolation.BondGraph.clusterPeaks_finite_of_mass_ne_top`, `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.critical_strip_null`, `OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound`, `OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth`, `OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio`, `OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_has_peak`, `OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top`, `OAI.CriticalPercolation.BondGraph.fresh_collar_transfer`, `OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae`, `OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae`, `OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial`, `OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self`, `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial`, `OAI.CriticalPercolation.BondGraph.normalizedClusterVolume_eq_at_peak`, `OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure`, `OAI.CriticalPercolation.BondGraph.restriction_incident_subset`, `OAI.CriticalPercolation.BondGraph.root_corridor_miss`, `OAI.CriticalPercolation.BondGraph.source_hit_probability`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_le_one_iff`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_ne_top`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_pos`, `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law`, `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks`, `OAI.CriticalPercolation.BondGraph.weighted_incidence_le` and `OAI.CriticalPercolation.FiniteClusters.restrict_cluster`; the proofs of `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.enn_fiber_sum`, `OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_enn_fiber_sum_bs`, `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.incoming_finite_ae`, `OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_incoming_finite_ae_bs`, `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal`, `OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_tilted_massTransport_ennreal_bs`, `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae`, `OAI_CriticalPercolation_BondGraph_atMostOneHeavy_critical_ae_bs`, `OAI.CriticalPercolation.BondGraph.atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.band_volume_peak`, `OAI_CriticalPercolation_BondGraph_band_volume_peak_bs`, `OAI.CriticalPercolation.BondGraph.band_volume_ratio`, `OAI_CriticalPercolation_BondGraph_band_volume_ratio_bs`, `OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end`, `OAI_CriticalPercolation_BondGraph_bondWeight_le_at_end_bs`, `OAI.CriticalPercolation.BondGraph.bondWeight_le_of_clusterPeak`, `OAI_CriticalPercolation_BondGraph_bondWeight_le_of_clusterPeak_bs`, `OAI.CriticalPercolation.BondGraph.bondWeight_ne_top`, `OAI_CriticalPercolation_BondGraph_bondWeight_ne_top_bs`, `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_le_one`, `OAI_CriticalPercolation_BondGraph_clusterPeakRatio_le_one_bs`, `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_ne_zero_of_mass_ne_top`, `OAI_CriticalPercolation_BondGraph_clusterPeakRatio_ne_zero_of_mass_ne_top_bs`, `OAI.CriticalPercolation.BondGraph.clusterPeaks_finite_of_mass_ne_top`, `OAI_CriticalPercolation_BondGraph_clusterPeaks_finite_of_mass_ne_top_bs`, `OAI_CriticalPercolation_BondGraph_critical_null_of_compact_open_orbital_quotient_bs`, `OAI.CriticalPercolation.BondGraph.critical_strip_null`, `OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound`, `OAI_CriticalPercolation_BondGraph_expected_discrepancyTail_bound_bs`, `OAI_CriticalPercolation_BondGraph_expected_discrepancy_peakBand_fourth_bs`, `OAI_CriticalPercolation_BondGraph_expected_heavy_normalizedDiscrepancy_bound_bs`, `OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio`, `OAI_CriticalPercolation_BondGraph_expected_weighted_peakRatio_bs`, `OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_has_peak`, `OAI_CriticalPercolation_BondGraph_finite_clusterUpperSet_has_peak_bs`, `OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top`, `OAI_CriticalPercolation_BondGraph_finite_clusterUpperSet_of_mass_ne_top_bs`, `OAI.CriticalPercolation.BondGraph.fresh_collar_transfer`, `OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae`, `OAI_CriticalPercolation_BondGraph_heavyRestrictedPeakTransport_incoming_ae_bs`, `OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae`, `OAI_CriticalPercolation_BondGraph_light_zero_or_infinitely_many_ae_bs`, `OAI_CriticalPercolation_BondGraph_main_failure_topological_classification_counterexample_bs`, `OAI_CriticalPercolation_BondGraph_main_light_or_sparse_polynomial_boundary_bs`, `OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self`, `OAI_CriticalPercolation_BondGraph_mem_clusterUpperSet_self_bs`, `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial`, `OAI_CriticalPercolation_BondGraph_nonunimodular_critical_mass_finite_ae_bs`, `OAI_CriticalPercolation_BondGraph_nonunimodular_critical_twoPoint_decay_bs`, `OAI_CriticalPercolation_BondGraph_nonunimodular_no_percolation_at_criticality_bs`, `OAI.CriticalPercolation.BondGraph.normalizedClusterVolume_eq_at_peak`, `OAI_CriticalPercolation_BondGraph_normalizedClusterVolume_eq_at_peak_bs`, `OAI.CriticalPercolation.BondGraph.restriction_incident_subset`, `OAI_CriticalPercolation_BondGraph_restriction_incident_subset_bs`, `OAI_CriticalPercolation_BondGraph_restriction_quadratic_real_le_bs`, `OAI_CriticalPercolation_BondGraph_restriction_weighted_quadratic_le_bs`, `OAI.CriticalPercolation.BondGraph.root_corridor_miss`, `OAI.CriticalPercolation.BondGraph.source_hit_probability`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base`, `OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base_bs`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_le_one_iff`, `OAI_CriticalPercolation_BondGraph_stabilizerWeight_le_one_iff_bs`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_ne_top`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_pos`, `OAI_CriticalPercolation_BondGraph_subcritical_seedExpectation_bound_bs`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn`, `OAI_CriticalPercolation_BondGraph_tendsto_expected_heavy_peakReturn_bs`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law`, `OAI_CriticalPercolation_BondGraph_tendsto_expected_signed_discrepancy_law_bs`, `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks`, `OAI_CriticalPercolation_BondGraph_uniform_lower_nestedLayer_blocks_bs`, `OAI.CriticalPercolation.BondGraph.weighted_incidence_le`, `OAI_CriticalPercolation_BondGraph_weighted_incidence_le_bs`, `OAI.CriticalPercolation.FiniteClusters.restrict_cluster`, `OAI_CriticalPercolation_HomogeneousAnalysis_Geometry_finite_stabilizer_harmonic_image_bs` and `OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree.linear_virtually_indicable`.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_CriticalPercolation

section
-- module Solutions.Q228_CP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Classification_AlgebraicDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

universe u

inductive AlgebraicDescent : (N : Type u) → [Group N] → Prop
  | finite (N : Type u) [Group N] [Finite N] : AlgebraicDescent N
  | cyclic (N : Type u) [Group N]
      (φ : N →* Multiplicative ℤ) (hφ : Surjective φ)
      (hf : (φ.ker : Set N).Finite) : AlgebraicDescent N
  | plane (N : Type u) [Group N]
      (φ : N →* Multiplicative (ℤ×ℤ)) (hφ : Surjective φ)
      (lower : ∀ J : Subgroup N, J≤φ.ker → AlgebraicDescent J) : AlgebraicDescent N

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_VertexBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem finite_neighbors (hlocal : G.LocallyFinite) (v : V) :
    (G.fullGraph.neighborSet v).Finite := by
  classical
  have hf : (⋃ e ∈ {e : E | v ∈ G.ends e}, (↑(G.ends e).toFinset : Set V)).Finite :=
    (hlocal v).biUnion fun e _ => (G.ends e).toFinset.finite_toSet
  apply hf.subset
  intro w hw
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hw
  apply Set.mem_iUnion₂.mpr
  refine ⟨e, ?_, ?_⟩ <;> simp [he]

def vertexBall (G : BondGraph V E) (o : V) : ℕ → Set V
  | 0 => {o}
  | n + 1 => G.vertexBall o n ∪ ⋃ v ∈ G.vertexBall o n, G.fullGraph.neighborSet v

lemma vertexBall_finite (hlocal : G.LocallyFinite) (o : V) (n : ℕ) :
    (G.vertexBall o n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton o
  | succ n ih => exact ih.union (ih.biUnion fun v _ => G.finite_neighbors hlocal v)

lemma reachable_mem_vertexBall {o v : V} (h : G.fullGraph.Reachable o v) :
    ∃ n, v ∈ G.vertexBall o n := by
  have hr := (G.fullGraph.reachable_iff_reflTransGen o v).mp h
  clear h
  induction hr with
  | refl => exact ⟨0, rfl⟩
  | @tail u w hr huv ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr (Set.mem_iUnion₂.mpr ⟨u, hn, huv⟩)⟩

def lengthReach (H : SimpleGraph V) : ℕ → V → V → Prop
  | 0, v, w => v = w
  | n + 1, v, w => ∃ u, lengthReach H n v u ∧ H.Adj u w

lemma reachable_iff_exists_lengthReach (H : SimpleGraph V) (v w : V) :
    H.Reachable v w ↔ ∃ n, lengthReach H n v w := by
  rw [H.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail u w h huw ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, u, hn, huw⟩
  · rintro ⟨n, hn⟩
    induction n generalizing w with
    | zero => exact hn ▸ Relation.ReflTransGen.refl
    | succ n ih =>
        obtain ⟨u, hu, huw⟩ := hn
        exact (ih u hu).tail huw

lemma measurable_openGraph_adj [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.openGraph ω).Adj v w) := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  exact (Measurable.exists fun e =>
    (measurable_set_mem e).and measurable_const).and measurable_const

lemma measurable_lengthReach [Countable V] [Countable E] (n : ℕ) (v w : V) :
    Measurable (fun ω : Set E => lengthReach (G.openGraph ω) n v w) := by
  induction n generalizing w with
  | zero => exact measurable_const
  | succ n ih =>
      exact Measurable.exists fun u => (ih u).and (G.measurable_openGraph_adj u w)

lemma measurable_reachable [Countable V] [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.openGraph ω).Reachable v w) := by
  simp_rw [reachable_iff_exists_lengthReach]
  exact Measurable.exists fun n => G.measurable_lengthReach n v w

@[simp] lemma openGraph_empty : G.openGraph ∅ = ⊥ := by
  simp [openGraph]

@[simp] lemma cluster_empty (v : V) : G.cluster ∅ v = {v} := by
  ext w
  simp [cluster, SimpleGraph.reachable_bot, eq_comm]

@[simp] lemma empty_not_percolates : ∅ ∉ G.percolates := by
  simp [percolates]

end BondGraph

namespace ClusterDeletion
variable {V : Type*}

def delete (H : SimpleGraph V) (U : Set V) : SimpleGraph V where
  Adj v w := H.Adj v w ∧ v ∉ U ∧ w ∉ U
  symm.symm _v _w h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl v h := H.loopless.irrefl v h.1

def roots (H : SimpleGraph V) (S : Set V) : Set V :=
  {v | ∃ s ∈ S, H.Reachable s v}

def component (H : SimpleGraph V) (s : V) : Set V :=
  {v | H.Reachable s v}

lemma roots_self (H : SimpleGraph V) (S : Set V) : S ⊆ roots H S :=
  fun s hs => ⟨s, hs, .refl _⟩

lemma roots_closed {H : SimpleGraph V} {S : Set V} {v w : V}
    (hv : v ∈ roots H S) (hvw : H.Adj v w) : w ∈ roots H S := by
  obtain ⟨s, hs, hsv⟩ := hv
  exact ⟨s, hs, hsv.trans hvw.reachable⟩

lemma reachable_mem_of_closed {H : SimpleGraph V} {U : Set V}
    (hU : ∀ ⦃v w⦄, v ∈ U → H.Adj v w → w ∈ U) {s v : V}
    (hs : s ∈ U) (hsv : H.Reachable s v) : v ∈ U := by
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact hs
  | tail _ huv ih => exact hU ih huv

lemma roots_subset_of_adj {H H' : SimpleGraph V} (S : Set V)
    (hh : ∀ ⦃v w⦄, v ∈ roots H S → H.Adj v w → H'.Adj v w) :
    roots H S ⊆ roots H' S := by
  rintro v ⟨s, hs, hsv⟩
  refine ⟨s, hs, ?_⟩
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact .refl _
  | @tail u v hr huv ih =>
      exact ih.trans (hh ⟨s, hs, (H.reachable_iff_reflTransGen s u).mpr hr⟩ huv).reachable

lemma roots_eq_of_adj_eq_incident {H H' : SimpleGraph V} {S U : Set V}
    (hU : roots H S = U)
    (hh : ∀ ⦃v w⦄, v ∈ U → (H.Adj v w ↔ H'.Adj v w)) :
    roots H' S = U := by
  subst U
  apply Set.Subset.antisymm
  · rintro v ⟨s, hs, hsv⟩
    exact reachable_mem_of_closed
      (fun {_ _} hv hvw => roots_closed hv ((hh hv).mpr hvw)) (roots_self H S hs) hsv
  · exact roots_subset_of_adj S fun {_ _} hv hvw => (hh hv).mp hvw

noncomputable def residual (H : SimpleGraph V) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact if s ∉ roots (delete H U) S then
    F (component (delete H (roots (delete H U) S)) s) -
      F (component (delete H (roots (delete H U) S ∪ U)) s)
  else 0

end ClusterDeletion
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def incidentEdges (U : Set V) : Set E := {e | ∃ v ∈ U, v ∈ G.ends e}

lemma openGraph_adj_eq_of_incident {U : Set V} {ω ω' : Set E}
    (hω : ∀ e ∈ G.incidentEdges U, e ∈ ω ↔ e ∈ ω') {v w : V} (hv : v ∈ U) :
    (G.openGraph ω).Adj v w ↔ (G.openGraph ω').Adj v w := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ G.incidentEdges U := by
    intro e heq
    exact ⟨v, hv, by simp [heq]⟩
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mpr heω, heq⟩, hne⟩

lemma roots_eq_of_incident {S U : Set V} {ω ω' : Set E}
    (hU : ClusterDeletion.roots (G.openGraph ω) S = U)
    (hω : ∀ e ∈ G.incidentEdges U, e ∈ ω ↔ e ∈ ω') :
    ClusterDeletion.roots (G.openGraph ω') S = U :=
  ClusterDeletion.roots_eq_of_adj_eq_incident hU (fun {_ _} hv => G.openGraph_adj_eq_of_incident hω hv)

end BondGraph
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_CutEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical

variable {V E : Type*}

def cutEdges (G : BondGraph V E) (O : Set V) : Set E :=
  {e | ∃ x y, G.ends e = s(x,y) ∧ x ∉ O ∧ y ∈ O}

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteInduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def inducedEdges (S : Set V) : Set E := {e | ∀ v ∈ G.ends e, v∈S}

def induce (S : Set V) : BondGraph S (G.inducedEdges S) where
  ends e := (G.ends e.val).attachWith e.property

lemma induce_ends_map (S : Set V) (e : G.inducedEdges S) :
    Sym2.map Subtype.val ((G.induce S).ends e) = G.ends e.val :=
  Sym2.attachWith_map_subtypeVal _

lemma induce_ends_eq (S : Set V) (e : G.inducedEdges S) (u v : S) :
    (G.induce S).ends e = s(u,v) ↔ G.ends e.val = s(u.val,v.val) := by
  rw [← G.induce_ends_map S e,← Sym2.map_mk]
  exact (Sym2.map.injective Subtype.val_injective).eq_iff.symm

lemma finite_incident (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.incidentEdges S).Finite := by
  have hh := hS.biUnion (fun v _ => hG v)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext e
  simp only [incidentEdges,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]

lemma finite_inducedEdges (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.inducedEdges S).Finite := by
  apply (G.finite_incident hG hS).subset
  intro e he
  obtain ⟨⟨u,v⟩,huv⟩ := Sym2.mk_surjective (G.ends e)
  have hu : u ∈ G.ends e := by rw [← huv]; simp
  exact ⟨u,he u hu,hu⟩

lemma induce_adj (S : Set V) (ω : Set (G.inducedEdges S)) (u v : S) :
    ((G.induce S).openGraph ω).Adj u v ↔
      (G.openGraph (Subtype.val '' ω)).Adj u.val v.val := by
  simp only [openGraph,SimpleGraph.fromEdgeSet_adj,Set.mem_image]
  constructor
  · rintro ⟨⟨e,he,hend⟩,hne⟩
    exact ⟨⟨e.val,⟨e,he,rfl⟩,(G.induce_ends_eq S e u v).mp hend⟩,
      fun h => hne (Subtype.ext h)⟩
  · rintro ⟨⟨e,⟨a,ha,rfl⟩,hend⟩,hne⟩
    exact ⟨⟨a,ha,(G.induce_ends_eq S a u v).mpr hend⟩,
      fun h => hne (congrArg Subtype.val h)⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def density (w : E → A → ℝ) (ω : E → A) : ℝ := ∏ e, w e (ω e)

noncomputable def expect (w : E → A → ℝ) (f : (E → A) → ℝ) : ℝ := by
  classical
  exact ∑ ω, density w ω * f ω

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_BitMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BernoulliProduct

noncomputable def bitMeasure (p : unitInterval) : Measure Prop :=
  unitInterval.toNNReal p • Measure.dirac True +
    unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False

instance bitMeasure_probability (p : unitInterval) : IsProbabilityMeasure (bitMeasure p) := by
  constructor
  simp [bitMeasure]

noncomputable def bitWeight (p : unitInterval) (b : Prop) : ℝ :=
  if b then p else 1-p

variable {E : Type*}

noncomputable def law (q : E → unitInterval) : Measure (Set E) :=
  Measure.map MeasurableEquiv.setOfPred (Measure.infinitePi fun e => bitMeasure (q e))

instance law_probability (q : E → unitInterval) : IsProbabilityMeasure (law q) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OpenGraphIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

instance law_probability (p : unitInterval) : IsProbabilityMeasure (G.law p) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma Aut.adj_map (φ : G.Aut) (ω : Set E) (v w : V) :
    (G.openGraph (φ.edge '' ω)).Adj (φ.vertex v) (φ.vertex w) ↔
      (G.openGraph ω).Adj v w := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  constructor
  · rintro ⟨⟨e, ⟨f, hf, rfl⟩, hend⟩, hne⟩
    rw [φ.preserves, ← Sym2.map_mk] at hend
    exact ⟨⟨f, hf, Sym2.map.injective φ.vertex.injective hend⟩,
      fun h => hne (congrArg φ.vertex h)⟩
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨φ.edge e, ⟨e, he, rfl⟩, ?_⟩, ?_⟩
    · rw [φ.preserves, hend, Sym2.map_mk]
    · exact fun h => hne (φ.vertex.injective h)

noncomputable def Aut.openGraphIso (φ : G.Aut) (ω : Set E) :
    G.openGraph ω ≃g G.openGraph (φ.edge '' ω) where
  toEquiv := φ.vertex
  map_rel_iff' := fun {v w} => Aut.adj_map G φ ω v w

def infiniteEvent (o : V) : Set (Set E) := {ω | (G.cluster ω o).Infinite}

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexBall_mono (o : V) : Monotone (G.vertexBall o) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

lemma mem_vertexBall_self (o : V) (n : ℕ) : o ∈ G.vertexBall o n :=
  G.vertexBall_mono o (Nat.zero_le n) rfl

lemma vertexBall_step {o v w : V} {n : ℕ} (hv : v ∈ G.vertexBall o n)
    (he : G.fullGraph.Adj v w) : w ∈ G.vertexBall o (n+1) :=
  Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,he⟩)

lemma vertexBall_add {o v : V} {n : ℕ} (hv : v ∈ G.vertexBall o n) (m : ℕ) :
    G.vertexBall v m ⊆ G.vertexBall o (n+m) := by
  induction m with
  | zero => simpa only [vertexBall,Nat.add_zero,Set.singleton_subset_iff] using hv
  | succ m ih =>
    rintro w (hw | hw)
    · exact G.vertexBall_mono o (by omega) (ih hw)
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hw
      exact G.vertexBall_step (ih hz) hzw

lemma vertexBall_comm {o v : V} {n : ℕ} : v ∈ G.vertexBall o n ↔ o ∈ G.vertexBall v n := by
  have h : ∀ n (o v : V), v ∈ G.vertexBall o n → o ∈ G.vertexBall v n := by
    intro n
    induction n with
    | zero => intro o v hv; simpa only [vertexBall,Set.mem_singleton_iff] using hv.symm
    | succ n ih =>
      intro o v hv
      rcases hv with hv | hv
      · exact G.vertexBall_mono v (Nat.le_succ n) (ih o v hv)
      · obtain ⟨z,hz,hzv⟩ := Set.mem_iUnion₂.mp hv
        have h1 : z ∈ G.vertexBall v 1 := G.vertexBall_step (G.mem_vertexBall_self v 0) hzv.symm
        simpa only [Nat.add_comm 1] using G.vertexBall_add h1 n (ih o z hz)
  exact ⟨h n o v,h n v o⟩

lemma Aut.fullGraph_adj (φ : G.Aut) (u v : V) :
    G.fullGraph.Adj (φ.vertex u) (φ.vertex v) ↔ G.fullGraph.Adj u v := by
  simpa only [fullGraph,Set.image_univ,Equiv.range_eq_univ] using Aut.adj_map G φ Set.univ u v

lemma Aut.vertexBall_mem (φ : G.Aut) (o v : V) (n : ℕ) :
    φ.vertex v ∈ G.vertexBall (φ.vertex o) n ↔ v ∈ G.vertexBall o n := by
  induction n generalizing v with
  | zero => simp only [vertexBall,Set.mem_singleton_iff,φ.vertex.injective.eq_iff]
  | succ n ih =>
    simp only [vertexBall,Set.mem_union,Set.mem_iUnion,exists_prop,SimpleGraph.mem_neighborSet]
    constructor
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mp h)
      · obtain ⟨w,rfl⟩ := φ.vertex.surjective z
        exact Or.inr ⟨w,(ih w).mp hz,
          (Aut.fullGraph_adj G φ w v).mp hzv⟩
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mpr h)
      · exact Or.inr ⟨φ.vertex z,(ih z).mpr hz,(Aut.fullGraph_adj G φ z v).mpr hzv⟩

lemma finite_subset_vertexBall (hconnected : G.fullGraph.Connected)
    (o : V) {S : Set V} (hS : S.Finite) : ∃ n, S ⊆ G.vertexBall o n := by
  have hh : ∀ v : S, ∃ n, v.val ∈ G.vertexBall o n :=
    fun v => G.reachable_mem_vertexBall (hconnected o v)
  choose n hn using hh
  let := hS.fintype
  refine ⟨∑ v : S, n v,?_⟩
  intro v hv
  exact G.vertexBall_mono o (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨v,hv⟩ : S))) (hn ⟨v,hv⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_UniformGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

protected def Aut.symm (φ : G.Aut) : G.Aut where
  vertex := φ.vertex.symm
  edge := φ.edge.symm
  preserves e := by
    have h := φ.preserves (φ.edge.symm e)
    have hh := congrArg (Sym2.map φ.vertex.symm) h
    simpa only [Equiv.apply_symm_apply,Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id',id_eq] using hh.symm

protected def Aut.trans (φ ψ : G.Aut) : G.Aut where
  vertex := φ.vertex.trans ψ.vertex
  edge := φ.edge.trans ψ.edge
  preserves e := by
    simp only [Equiv.trans_apply,ψ.preserves,φ.preserves,Sym2.map_map]
    rfl

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_HeightCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def heightCut (π : V → ℤ) (t : ℤ) : Set E := G.cutEdges {v | t < π v}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_TailProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

abbrev coordinateSigma (e : E) : MeasurableSpace (Set E) :=
  MeasurableSpace.comap (fun ω : Set E => e ∈ ω) inferInstance

abbrev blockSigma (S : Set E) : MeasurableSpace (Set E) := ⨆ e ∈ S, coordinateSigma e

lemma coordinateSigma_le (e : E) : coordinateSigma e ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  (measurable_set_mem e).comap_le

lemma blockSigma_le (S : Set E) : blockSigma S ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  iSup₂_le fun e _ => coordinateSigma_le e

def forceOn (S : Set E) (σ ω : Set E) : Set E := fun e => if e ∈ S then e ∈ σ else e ∈ ω

lemma measurable_forceOn_block (S σ : Set E) :
    @Measurable (Set E) (Set E) (blockSigma Sᶜ) inferInstance (forceOn S σ) := by
  refine (@measurable_pi_iff (Set E) E (fun _ => Prop) (blockSigma Sᶜ)
    (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e ∈ S
  · simpa only [forceOn, ite_eq_left he] using
      (@measurable_const Prop (Set E) inferInstance (blockSigma Sᶜ) (e ∈ σ))
  · have hm : @Measurable (Set E) Prop (coordinateSigma e) inferInstance
        (fun ω => e ∈ ω) := measurable_iff_comap_le.mpr le_rfl
    have hl : coordinateSigma e ≤ blockSigma Sᶜ := le_iSup_of_le e (le_iSup_of_le he le_rfl)
    simpa only [forceOn, ite_eq_right he] using hm.mono hl le_rfl

lemma measurable_forceOn (S σ : Set E) : Measurable (forceOn S σ) :=
  (measurable_forceOn_block S σ).mono (blockSigma_le Sᶜ) le_rfl

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BlockIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

def closedBlock (S : Set E) : Set (Set E) := {ω | Disjoint S ω}

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphActionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]

def PreservesEnds : Prop :=
  ∀ (g : Λ) (e : E), G.ends (g • e)=Sym2.map (fun v : V => g • v) (G.ends e)

def smulAut (h : G.PreservesEnds (Λ := Λ)) (g : Λ) : G.Aut where
  vertex := MulAction.toPerm g
  edge := MulAction.toPerm g
  preserves := h g

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteIndexAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ Q : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

def quotientSubgroupMap (ρ : Λ →* Q) (N : Subgroup Q) : N.comap ρ →* N where
  toFun g := ⟨ρ g.val,g.property⟩
  map_one' := Subtype.ext (ρ.map_one)
  map_mul' g h := Subtype.ext (ρ.map_mul g.val h.val)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[ext] lemma Aut.ext {f g : G.Aut} (hv : f.vertex=g.vertex) (he : f.edge=g.edge) : f=g := by
  cases f
  cases g
  cases hv
  cases he
  rfl

instance instGroupAut : Group G.Aut where
  one := ⟨Equiv.refl V,Equiv.refl E,by intro e; simp⟩
  mul f g := Aut.trans G g f
  inv f := Aut.symm G f
  mul_assoc f g h := by apply Aut.ext G <;> rfl
  one_mul f := by apply Aut.ext G <;> rfl
  mul_one f := by apply Aut.ext G <;> rfl
  inv_mul_cancel f := by
    apply Aut.ext G <;> apply Equiv.ext <;> intro x <;>
      exact Equiv.symm_apply_apply _ x

instance instMulActionAut : MulAction G.Aut V where
  smul f x := f.vertex x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma Aut.smul_vertex (f : G.Aut) (x : V) : f • x=f.vertex x := rfl

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitalPower
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def powerOn (O : Set V) (L : ℕ) : SimpleGraph O where
  Adj u v := u≠v ∧ v.val∈G.vertexBall u.val L
  symm := ⟨fun _ _ h => ⟨h.1.symm,G.vertexBall_comm.mp h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitPower (o : V) (L : ℕ) : SimpleGraph (MulAction.orbit G.Aut o) :=
  G.powerOn (MulAction.orbit G.Aut o) L

def orbitPowerHom (o : V) (L : ℕ) : G.Aut →*
    (G.orbitPower o L ≃g G.orbitPower o L) where
  toFun φ :=
    { toEquiv := MulAction.toPerm φ
      map_rel_iff' := by
        intro x y
        change (φ • x≠φ • y ∧ (φ • y).val∈G.vertexBall (φ • x).val L) ↔
          (x≠y ∧ y.val∈G.vertexBall x.val L)
        exact and_congr (MulAction.toPerm φ).injective.ne_iff
          (Aut.vertexBall_mem G φ x.val y.val L) }
  map_one' := by apply RelIso.ext; intro x; change (1 : G.Aut) • x=x; exact one_smul _ _
  map_mul' φ ψ := by
    apply RelIso.ext; intro x
    change (φ*ψ) • x=φ • (ψ • x)
    exact mul_smul _ _ _

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_OrbitalNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical Pointwise

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitBall (o : V) (r : ℕ) : Set V :=
  MulAction.orbit G.Aut o ∩ G.vertexBall o r

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteProductPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def pin (w : E → A → ℝ) (e : E) (b : A) : E → A → ℝ :=
  Function.update w e (fun a => if a = b then 1 else 0)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def distribution {B : Type*} [DecidableEq B]
    (w : E → A → ℝ) (φ : (E → A) → B) (b : B) : ℝ :=
  expect w (fun ω => if φ ω = b then 1 else 0)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def prob (w : E → Prop → ℝ) (P : Set E → Prop) : ℝ :=
  expect w (fun ω => if P ω then 1 else 0)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Delta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def delta (w : E → Prop → ℝ) (F : Set E → Prop) (e : E) : ℝ :=
  prob (pin w e True) F - prob (pin w e False) F

def openPivot (F : Set E → Prop) (e : E) (ω : Set E) : Prop :=
  ω e ∧ F ω ∧ ¬F (Function.update ω e False)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ProductConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

@[simp] lemma mem_forceOn (S σ ω : Set E) (e : E) :
    e∈forceOn S σ ω ↔ if e∈S then e∈σ else e∈ω := Iff.rfl

lemma measurable_forceOn_joint_block (S : Set E) :
    @Measurable (Set E × Set E) (Set E)
      ((blockSigma S).prod inferInstance) inferInstance
      (fun z => forceOn S z.1 z.2) := by
  refine (@measurable_pi_iff (Set E × Set E) E (fun _ => Prop)
    ((blockSigma S).prod inferInstance) (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e∈S
  · have hm : @Measurable (Set E) Prop (blockSigma S) inferInstance
        (fun σ => e∈σ) := by
      apply measurable_iff_comap_le.mpr
      exact le_iSup_of_le e (le_iSup_of_le he le_rfl)
    simpa only [forceOn,ite_eq_left he,Function.comp_def] using hm.comp measurable_fst
  · simpa only [forceOn,ite_eq_right he,Function.comp_def] using (measurable_set_mem e).comp measurable_snd

def pinnedParameters (q : E → unitInterval) (S σ : Set E) : E → unitInterval :=
  fun e => if e∈S then if e∈σ then 1 else 0 else q e

def blockProbability (q : E → unitInterval) (S : Set E) (A : Set (Set E))
    (σ : Set E) : ℝ≥0∞ := law q ((forceOn S σ) ⁻¹' A)

lemma blockProbability_eq_lintegral (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (σ : Set E) :
    blockProbability q S A σ=∫⁻ ω, A.indicator (1 : Set E → ℝ≥0∞) (forceOn S σ ω) ∂law q := by
  unfold blockProbability
  rw [← lintegral_indicator_one (hA.preimage (measurable_forceOn S σ))]
  rfl

lemma measurable_blockProbability (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance (blockProbability q S A) := by
  have hI : @Measurable (Set E × Set E) ℝ≥0∞
      ((blockSigma S).prod Set.instMeasurableSpace) inferInstance
      (fun z => A.indicator (1 : Set E → ℝ≥0∞) (forceOn S z.1 z.2)) :=
    @Measurable.comp (Set E × Set E) (Set E) ℝ≥0∞
      ((blockSigma S).prod Set.instMeasurableSpace) Set.instMeasurableSpace inferInstance
      _ _ (measurable_const.indicator hA) (measurable_forceOn_joint_block S)
  have hm := @Measurable.lintegral_prod_right' (Set E) (Set E)
    (blockSigma S) Set.instMeasurableSpace (law q) inferInstance _ hI
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext σ
  exact blockProbability_eq_lintegral q S A hA σ

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_FreshTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def allOpen (F : Set E) : Set (Set E) := {ω | F⊆ω}

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_HitValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V : Type*}

noncomputable def hitValue (A U : Set V) : ℝ := if (U ∩ A).Nonempty then 1 else 0
noncomputable def jointHitValue (A T U : Set V) : ℝ :=
  if (U ∩ A).Nonempty ∧ (U ∩ T).Nonempty then 1 else 0

end CriticalPercolation.ClusterColumns

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_Earlier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V : Type*} {n : ℕ}

def earlier (x : Fin n → V) (k : Fin n) : Set V := {v | ∃ j < k, x j = v}
def first (H : SimpleGraph V) (x : Fin n → V) (k : Fin n) : Prop :=
  x k ∉ roots H (earlier x k)
noncomputable def select (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) : ℝ :=
  if first H x k ∧ x i ∈ component H (x k) then 1 else 0

end CriticalPercolation.ClusterColumns

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ExpectedCluster
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def expectedCluster (w : E → Prop → ℝ) (s : V)
    (F : Set V → ℝ) (W : Set V) : ℝ :=
  expect w (fun ω => F (component (delete (G.openGraph ω) W) s))

noncomputable def expectedResidual (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact expect w (fun ω =>
    if s ∉ roots (delete (G.openGraph ω) U) S then
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S ∪ U)
    else 0)

end CriticalPercolation.BondGraph

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterUpdate
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

open scoped Classical

noncomputable def clusterUpdate (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ :=
  expect w (fun ω => G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S))

noncomputable def avoidedAverage (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) : ℝ := by
  classical
  exact expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
    F (component (G.openGraph ω) s) else 0)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_DeleteBot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}
@[simp] lemma delete_bot (U : Set V) : delete (⊥ : SimpleGraph V) U = ⊥ := by
  ext v w
  simp [delete]
@[simp] lemma component_bot (s : V) : component (⊥ : SimpleGraph V) s = {s} := by
  ext v
  simp [component, SimpleGraph.reachable_bot, eq_comm]
@[simp] lemma roots_bot (S : Set V) : roots (⊥ : SimpleGraph V) S = S := by
  ext v
  simp [roots, SimpleGraph.reachable_bot]
end CriticalPercolation.ClusterDeletion

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_HitOthers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open scoped Classical

variable {V : Type*} {n : ℕ}

noncomputable def hitOthers (x : Fin n → V) (k : Fin n) (U : Set V) : ℝ :=
  if ∃ j, j ≠ k ∧ x j ∈ U then 1 else 0

end CriticalPercolation.ClusterColumns

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Column
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def column {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) (i : Fin n) : ℝ :=
  expect w (fun ω => select (G.openGraph ω) x k i * F (component (G.openGraph ω) (x k)))

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_UpdateKernel
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def updateKernel (w : E → Prop → ℝ) (S : Set V) (s : V)
    (U Z : Set V) : ℝ :=
  G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0) U

noncomputable def avoidedLaw (w : E → Prop → ℝ) (S : Set V) (s : V) (U : Set V) : ℝ :=
  G.avoidedAverage w S s (fun Z => if Z = U then 1 else 0) /
    G.avoidedAverage w S s (fun _ => 1)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_ClusterMatrix
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def clusterMatrix {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    Matrix (Fin n) (Fin n) ℝ := fun i k => G.column w x k (fun _ => 1) i

noncomputable def inverseColumn {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) : Fin n → ℝ :=
  (G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k F

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_RestrictVertices
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

noncomputable def restrictVertices (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) : BondGraph U E where
  ends e := (G.ends e).attachWith (hU e)

open CriticalPercolation.ClusterColumns CriticalPercolation.ClusterDeletion
open CriticalPercolation.FiniteProduct

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def hitEvent (o : V) (A : Set V) : Set (Set E) :=
  {ω | (G.cluster ω o ∩ A).Nonempty}

lemma measurableSet_hitEvent [Countable V] [Countable E] (o : V) (A : Set V) :
    MeasurableSet (G.hitEvent o A) := by
  exact (Measurable.exists fun v => (G.measurable_reachable o v).and measurable_const).setOf

def restrictEdges (s : Set E) : BondGraph V s where
  ends e := G.ends e

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ConditionalGluing
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def seedHitEvent (B T : Set V) : Set (Set E) :=
  ⋃ b∈B, G.hitEvent b T

lemma measurableSet_seedHitEvent [Countable V] [Countable E] (B T : Set V) :
    MeasurableSet (G.seedHitEvent B T) :=
  MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => G.measurableSet_hitEvent b T

def goodRelay (q : E → unitInterval) (S : Set E) (L : Set V)
    (F : V → Set E) (B : V → Set V) (T : Set V) (lam : ℝ) (σ : Set E) : Set V :=
  {v | v∈L ∧ F v⊆σ ∧ 1-lam≤(blockProbability q S (G.seedHitEvent (B v) T) σ).toReal}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CollarDistance
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def vertexCollar (B : Set V) (n : ℕ) : Set V := ⋃ b∈B, G.vertexBall b n

def distanceTo (B : Set V) (v : V) : ℕ :=
  if h : ∃ n, v∈G.vertexCollar B n then Nat.find h else 0

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Corridor

abbrev Site := ℤ×ℤ
abbrev Point := ℝ×ℝ
abbrev Edge := Site×Bool

def source (e : Edge) : Site := e.1
def target (e : Edge) : Site := if e.2 then e.1+(1,0) else e.1+(0,1)

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Relay

def width (i : ℕ) : ℝ := max 2 (210-(i : ℝ)/2)

def domain (J T σ : ℝ) : Set (ℝ×ℝ) :=
  {x | |x.1| ≤ J ∧ |x.2| ≤ J/4+630} ∪
  {x | |x.1-T| ≤ J ∧ |x.2-σ*T/4| ≤ J/4+630} ∪
  {x | 0 ≤ x.1 ∧ x.1 ≤ T ∧ |x.2-σ*x.1/4| ≤ 630}

end CriticalPercolation.Relay
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayMoves
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma open_induced_adj (S : Set V) (ω : Set E) (u v : V) :
    (G.openGraph (ω∩G.inducedEdges S)).Adj u v ↔
    (G.openGraph ω).Adj u v ∧ u∈S ∧ v∈S := by
  constructor
  · rintro ⟨⟨b,hb,hend⟩,hne⟩
    exact ⟨⟨⟨b,hb.1,hend⟩,hne⟩,hb.2 u (by rw [hend]; simp),
      hb.2 v (by rw [hend]; simp)⟩
  · rintro ⟨⟨⟨b,hb,hend⟩,hne⟩,hu,hv⟩
    refine ⟨⟨b,⟨hb,?_⟩,hend⟩,hne⟩
    intro w hw
    rw [hend] at hw
    rcases (Sym2.mem_iff.mp hw) with rfl|rfl <;> assumption

def coordinateMove (t z : V → ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.vertexBall y m, ∃ b, ∃ w : (G.openGraph ω).Walk a b,
    (∀ x∈w.support, |t x-t y| ≤ 100 ∧ |z x-z y| ≤ 100) ∧
    |t b-(t y+1)| ≤ e/4 ∧ |z b-(z y+s)| ≤ e/4}

def relayRegion (t z : V → ℝ) (σ e : ℝ) (i : ℕ) : Set V :=
  {v | |t v-(i : ℝ)| ≤ (i+1)*e ∧ |z v-σ*(i : ℝ)/4| ≤ Relay.width i}

def relayMark (t z : V → ℝ) (T σ ρ : ℝ) : Set V :=
  {v | T ≤ t v ∧ t v ≤ T+ρ ∧ |z v-σ*T/4| ≤ 210}

def relayDomain (t z : V → ℝ) (J T σ : ℝ) : Set V :=
  (fun v => (t v,z v)) ⁻¹' Relay.domain J T σ

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_OpenRay
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure OpenRay (ω : Set E) where
  vertex : ℕ → V
  injective : Function.Injective vertex
  adjacent : ∀ n, (G.openGraph ω).Adj (vertex n) (vertex (n+1))

@[ext]
structure RayPrefix (ω : Set E) (o : V) (n : ℕ) where
  vertex : Fin (n+1) → V
  start : vertex 0=o
  adjacent : ∀ i : Fin n, (G.openGraph ω).Adj (vertex i.castSucc) (vertex i.succ)
  injective : Function.Injective vertex
  ball : ∀ i, vertex i∈G.vertexBall o i.val

def RayPrefix.restrict {ω : Set E} {o : V} {i j : ℕ} (h : i≤j)
    (p : G.RayPrefix ω o j) : G.RayPrefix ω o i where
  vertex k := p.vertex (Fin.castLE (Nat.succ_le_succ h) k)
  start := p.start
  adjacent k := p.adjacent (Fin.castLE h k)
  injective := by
    intro x y heq
    exact Fin.ext (congrArg (fun z : Fin (j+1) => z.val) (p.injective heq))
  ball k := p.ball (Fin.castLE (Nat.succ_le_succ h) k)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_SubexponentialVolumes
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def SubexponentialGrowth : Prop :=
  ∀ o : V, ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n≥N,
    Real.log ((G.vertexBall o n).ncard : ℝ) ≤ ε*n

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ComponentCritical
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma image_restrict (S : Set V) (ω : Set E) :
    Subtype.val '' (Subtype.val ⁻¹' ω : Set (G.inducedEdges S))=ω∩G.inducedEdges S := by
  ext e
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,a.property⟩
  · rintro ⟨he,hs⟩
    exact ⟨⟨e,hs⟩,he,rfl⟩

def domainComponent (S : Set V) (o : V) : Set V := G.cluster (G.inducedEdges S) o

def OpenRay.induce {ω : Set E} (r : G.OpenRay ω) (S : Set V)
    (hS : ∀ n, r.vertex n∈S) :
    (G.induce S).OpenRay (Subtype.val ⁻¹' ω) where
  vertex n := ⟨r.vertex n,hS n⟩
  injective := fun _ _ h => r.injective (congrArg Subtype.val h)
  adjacent n := by
    apply (G.induce_adj S (Subtype.val ⁻¹' ω) _ _).mpr
    rw [G.image_restrict]
    exact (G.open_induced_adj S ω _ _).mpr ⟨r.adjacent n,hS n,hS (n+1)⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_InducedAutomorphism
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.inducedEdges_mem (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (e : E) :
    phi.edge e∈G.inducedEdges S ↔ e∈G.inducedEdges S := by
  constructor
  · intro h x hx
    apply (hS x).mp
    apply h (phi.vertex x)
    rw [phi.preserves]
    exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩
  · intro h y hy
    rw [phi.preserves] at hy
    obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hy
    exact (hS x).mpr (h x hx)

def Aut.restrict (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) : (G.induce S).Aut where
  vertex :=
    { toFun := fun x => ⟨phi.vertex x,(hS x).mpr x.property⟩
      invFun := fun x => ⟨phi.vertex.symm x,(hS (phi.vertex.symm x)).mp
        (by simpa only [Equiv.apply_symm_apply] using x.property)⟩
      left_inv := fun x => Subtype.ext (phi.vertex.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (phi.vertex.apply_symm_apply x) }
  edge :=
    { toFun := fun e => ⟨phi.edge e,(Aut.inducedEdges_mem G phi S hS e).mpr e.property⟩
      invFun := fun e => ⟨phi.edge.symm e,(Aut.inducedEdges_mem G phi S hS (phi.edge.symm e)).mp
        (by simpa only [Equiv.apply_symm_apply] using e.property)⟩
      left_inv := fun e => Subtype.ext (phi.edge.symm_apply_apply e)
      right_inv := fun e => Subtype.ext (phi.edge.apply_symm_apply e) }
  preserves e := by
    apply Sym2.map.injective Subtype.val_injective
    rw [G.induce_ends_map,Sym2.map_map]
    change G.ends (phi.edge e.val)=Sym2.map (fun x : S => phi.vertex x.val) ((G.induce S).ends e)
    calc
      G.ends (phi.edge e.val)=Sym2.map phi.vertex (G.ends e.val) := phi.preserves e.val
      _=Sym2.map phi.vertex (Sym2.map (Subtype.val : S → V) ((G.induce S).ends e)) :=
        congrArg (Sym2.map phi.vertex) (G.induce_ends_map S e).symm
      _=_ := Sym2.map_map _

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_RestrictedAction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]

def domainPreserver (C : Set V) : Subgroup Λ where
  carrier := {g | ∀ x, g • x∈C ↔ x∈C}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg x
    simpa only [smul_inv_smul] using (hg (g⁻¹ • x)).symm

@[instance_reducible] def restrictedVertexAction (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    MulAction L C where
  smul g x := ⟨(g : Λ) • x.val,(hL g.property x.val).mpr x.property⟩
  one_smul x := Subtype.ext (one_smul Λ x.val)
  mul_smul g h x := Subtype.ext (mul_smul (g : Λ) (h : Λ) x.val)

@[instance_reducible] def restrictedEdgeAction (ha : G.PreservesEnds (Λ := Λ))
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    MulAction L (G.inducedEdges C) where
  smul g e := ⟨(g : Λ) • e.val,
    (Aut.inducedEdges_mem G (G.smulAut ha g.val) C (hL g.property) e.val).mpr e.property⟩
  one_smul e := Subtype.ext (one_smul Λ e.val)
  mul_smul g h e := Subtype.ext (mul_smul (g : Λ) (h : Λ) e.val)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ComponentAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ T : Type*} (G : BondGraph V E)
  [Group Λ] [Group T] [MulAction Λ V] [MulAction Λ E]

def componentKernel (a : Λ →* T) (C : Set V) : Subgroup Λ :=
  a.ker ⊓ domainPreserver C

lemma componentKernel_le (a : Λ →* T) (C : Set V) :
    componentKernel a C≤domainPreserver C := inf_le_right

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ActionOrbitTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace ActionOrbitTransport
variable (Λ X : Type*) [Group Λ] [MulAction Λ X]

abbrev PairOrbit := MulAction.orbitRel.Quotient Λ (X × X)
def pairOrbit (x y : X) : PairOrbit Λ X := Quotient.mk'' (x,y)
def stabilizerOrbit (x y : X) : Set X := MulAction.orbit (MulAction.stabilizer Λ x) y
def suborbitCard (x y : X) : ℕ := (stabilizerOrbit Λ X x y).ncard

lemma mem_stabilizerOrbit {x y z : X} : z ∈ stabilizerOrbit Λ X x y ↔
    ∃ φ : Λ, φ • x = x ∧ φ • y = z := by
  simp only [stabilizerOrbit,MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨φ,hφ⟩
    exact ⟨φ,φ.property,hφ⟩
  · rintro ⟨φ,hx,hy⟩
    exact ⟨⟨φ,hx⟩,hy⟩

lemma pairOrbit_eq {x y u v : X} : pairOrbit Λ X x y = pairOrbit Λ X u v ↔
    ∃ φ : Λ, φ • x = u ∧ φ • y = v := by
  constructor
  · intro h
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
    exact ⟨φ,congrArg Prod.fst hφ,congrArg Prod.snd hφ⟩
  · rintro ⟨φ,hx,hy⟩
    apply Eq.symm
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext hx hy⟩

lemma smul_pairOrbit (φ : Λ) (x y : X) :
    pairOrbit Λ X (φ • x) (φ • y) = pairOrbit Λ X x y :=
  (pairOrbit_eq Λ X |>.mpr ⟨φ,rfl,rfl⟩).symm

end ActionOrbitTransport
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_Unimodularity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure UnimodularRoot where
  roots : Finset V
  weight : V → ℝ
  positive : ∀ u ∈ roots, 0 < weight u
  normalized : ∑ u ∈ roots, weight u = 1
  cover : ∀ v : V, ∃ u ∈ roots, ∃ φ : G.Aut, φ.vertex u = v
  balance : ∀ F : V → V → ℝ,
    (∀ (φ : G.Aut) u v, F (φ.vertex u) (φ.vertex v) = F u v) →
    (∀ u, (Function.support (F u)).Finite) →
    (∀ v, (Function.support (fun u => F u v)).Finite) →
    (∑ u ∈ roots, weight u * ∑' v, F u v) =
      ∑ v ∈ roots, weight v * ∑' u, F u v

def bondShare (e : E) : ℝ := 1 / (G.ends e).toFinset.card

def splitBondTransport (F : V → E → ℝ) (u v : V) : ℝ :=
  ∑' e, if v ∈ G.ends e then G.bondShare e * F u e else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_RelativeModular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace Subgroup
open scoped _root_.Subgroup
variable {Γ : Type*} [Group Γ]

def relativeMass (A B : Subgroup Γ) : ℝ := (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

lemma relativeMass_eq_of_le {I A B : Subgroup Γ} (hIA : I ≤ A) (hIB : I ≤ B)
    (hI : I.relIndex A ≠ 0) :
    relativeMass A B = (I.relIndex A : ℝ) / (I.relIndex B : ℝ) := by
  have ha := _root_.Subgroup.relIndex_mul_relIndex I (A ⊓ B) A (le_inf hIA hIB) inf_le_left
  have hb := _root_.Subgroup.relIndex_mul_relIndex I (A ⊓ B) B (le_inf hIA hIB) inf_le_right
  have hi : I.relIndex (A ⊓ B) ≠ 0 := by
    intro hi
    rw [hi,zero_mul] at ha
    exact hI ha.symm
  have hir : (I.relIndex (A ⊓ B) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  rw [_root_.Subgroup.inf_relIndex_left] at ha
  rw [_root_.Subgroup.inf_relIndex_right] at hb
  unfold relativeMass
  calc
    _ = ((I.relIndex (A ⊓ B) : ℝ) * (B.relIndex A : ℝ)) /
        ((I.relIndex (A ⊓ B) : ℝ) * (A.relIndex B : ℝ)) :=
      (mul_div_mul_left _ _ hir).symm
    _ = _ := by simp only [← Nat.cast_mul,ha,hb]

lemma relativeMass_cocycle (A B C : Subgroup Γ)
    (hab : A.relIndex B ≠ 0) (hba : B.relIndex A ≠ 0)
    (hca : C.relIndex A ≠ 0) (hcb : C.relIndex B ≠ 0) :
    relativeMass A B * relativeMass B C = relativeMass A C := by
  let I := A ⊓ B ⊓ C
  have hIA : I ≤ A := inf_le_left.trans inf_le_left
  have hIB : I ≤ B := inf_le_left.trans inf_le_right
  have hIC : I ≤ C := inf_le_right
  have hI0A : I.relIndex A ≠ 0 :=
    _root_.Subgroup.relIndex_inf_ne_zero (by simpa only [_root_.Subgroup.inf_relIndex_left] using hba) hca
  have hI0B : I.relIndex B ≠ 0 :=
    _root_.Subgroup.relIndex_inf_ne_zero (by simpa only [_root_.Subgroup.inf_relIndex_right] using hab) hcb
  rw [relativeMass_eq_of_le hIA hIB hI0A,relativeMass_eq_of_le hIB hIC hI0B,
    relativeMass_eq_of_le hIA hIC hI0A]
  exact div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr hI0B)

lemma relativeMass_self (A : Subgroup Γ) : relativeMass A A = 1 := by
  simp [relativeMass]

end Subgroup
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_GraphModular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stabilizerOrbit (x y : V) : Set V :=
  MulAction.orbit (MulAction.stabilizer G.Aut x) y

lemma mem_stabilizerOrbit {x y z : V} : z ∈ G.stabilizerOrbit x y ↔
    ∃ φ : G.Aut, φ.vertex x = x ∧ φ.vertex y = z := by
  simp only [stabilizerOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨φ,hφ⟩
    exact ⟨φ,φ.property,hφ⟩
  · rintro ⟨φ,hx,hy⟩
    exact ⟨⟨φ,hx⟩,hy⟩

lemma self_mem_stabilizerOrbit (x y : V) : y ∈ G.stabilizerOrbit x y :=
  (G.mem_stabilizerOrbit).mpr ⟨1,rfl,rfl⟩

lemma stabilizerOrbit_finite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : (G.stabilizerOrbit x y).Finite := by
  obtain ⟨n,hn⟩ := G.finite_subset_vertexBall hc x (Set.finite_singleton y)
  apply (G.vertexBall_finite hl x n).subset
  intro z hz
  obtain ⟨φ,hx,rfl⟩ := G.mem_stabilizerOrbit.mp hz
  rw [←hx]
  exact (Aut.vertexBall_mem G φ x y n).mpr (hn (Set.mem_singleton y))

def suborbitCard (x y : V) : ℕ := (G.stabilizerOrbit x y).ncard

lemma suborbitCard_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : 0 < G.suborbitCard x y :=
  (Set.ncard_pos (G.stabilizerOrbit_finite hc hl x y)).mpr ⟨y,G.self_mem_stabilizerOrbit x y⟩

lemma suborbitCard_eq_relIndex (x y : V) : G.suborbitCard x y =
    (MulAction.stabilizer G.Aut y).relIndex (MulAction.stabilizer G.Aut x) := by
  have heq : (MulAction.stabilizer G.Aut y).subgroupOf (MulAction.stabilizer G.Aut x) =
      MulAction.stabilizer (MulAction.stabilizer G.Aut x) y := by
    ext φ
    rfl
  rw [Subgroup.relIndex,heq,MulAction.index_stabilizer]
  rfl

lemma Aut.stabilizerOrbit_image (φ : G.Aut) (x y : V) :
    φ.vertex '' G.stabilizerOrbit x y = G.stabilizerOrbit (φ.vertex x) (φ.vertex y) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨ψ,hx,hy⟩ := G.mem_stabilizerOrbit.mp hw
    apply G.mem_stabilizerOrbit.mpr
    refine ⟨φ * ψ * φ⁻¹,?_,?_⟩
    · change φ.vertex (ψ.vertex (φ.vertex.symm (φ.vertex x))) = φ.vertex x
      rw [Equiv.symm_apply_apply,hx]
    · change φ.vertex (ψ.vertex (φ.vertex.symm (φ.vertex y))) = φ.vertex w
      rw [Equiv.symm_apply_apply,hy]
  · intro hz
    obtain ⟨ψ,hx,hy⟩ := G.mem_stabilizerOrbit.mp hz
    refine ⟨φ.vertex.symm z,?_,φ.vertex.apply_symm_apply z⟩
    apply G.mem_stabilizerOrbit.mpr
    refine ⟨φ⁻¹ * ψ * φ,?_,?_⟩
    · change φ.vertex.symm (ψ.vertex (φ.vertex x)) = x
      rw [hx,Equiv.symm_apply_apply]
    · change φ.vertex.symm (ψ.vertex (φ.vertex y)) = φ.vertex.symm z
      rw [hy]

lemma Aut.suborbitCard (φ : G.Aut) (x y : V) :
    G.suborbitCard (φ.vertex x) (φ.vertex y) = G.suborbitCard x y := by
  rw [CriticalPercolation.BondGraph.suborbitCard,←Aut.stabilizerOrbit_image G φ,
      Set.ncard_image_of_injective _ φ.vertex.injective]
  rfl

def modularRatio (x y : V) : ℝ := (G.suborbitCard x y : ℝ) / (G.suborbitCard y x : ℝ)

lemma modularRatio_eq_relativeMass (x y : V) : G.modularRatio x y =
    Subgroup.relativeMass (MulAction.stabilizer G.Aut x) (MulAction.stabilizer G.Aut y) := by
  simp only [modularRatio,suborbitCard_eq_relIndex,Subgroup.relativeMass]

lemma modularRatio_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    0 < G.modularRatio x y :=
  div_pos (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl x y))
    (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x))

lemma modularRatio_cocycle (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y z : V) : G.modularRatio x y * G.modularRatio y z = G.modularRatio x z := by
  simp only [modularRatio_eq_relativeMass]
  apply Subgroup.relativeMass_cocycle
  all_goals
    rw [←suborbitCard_eq_relIndex]
    exact ne_of_gt (G.suborbitCard_pos hc hl _ _)

lemma modularRatio_self (x : V) : G.modularRatio x x = 1 := by
  rw [modularRatio_eq_relativeMass,Subgroup.relativeMass_self]

lemma Aut.modularRatio (φ : G.Aut) (x y : V) :
    G.modularRatio (φ.vertex x) (φ.vertex y) = G.modularRatio x y := by
  simp only [CriticalPercolation.BondGraph.modularRatio,Aut.suborbitCard]

def CombinatoriallyUnimodular : Prop :=
  ∀ (φ : G.Aut) x, G.suborbitCard x (φ.vertex x) = G.suborbitCard (φ.vertex x) x

lemma CombinatoriallyUnimodular.modularRatio (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (φ : G.Aut) (x : V) :
    G.modularRatio x (φ.vertex x) = 1 := by
  simp only [CriticalPercolation.BondGraph.modularRatio,hu φ x,
    div_self (ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl (φ.vertex x) x)) :
      (G.suborbitCard (φ.vertex x) x : ℝ) ≠ 0)]

lemma CombinatoriallyUnimodular.rootWeight_invariant (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (o : V) (φ : G.Aut) (x : V) :
    G.modularRatio o (φ.vertex x) = G.modularRatio o x := by
  rw [← G.modularRatio_cocycle hc hl o (φ.vertex o) (φ.vertex x),
    CombinatoriallyUnimodular.modularRatio G hu hc hl φ o,one_mul,Aut.modularRatio]

lemma modularRatio_card_balance (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x y : V) : G.modularRatio o x * (G.suborbitCard x y : ℝ) =
      G.modularRatio o y * (G.suborbitCard y x : ℝ) := by
  have hh := G.modularRatio_cocycle hc hl o x y
  unfold modularRatio at hh
  rw [← mul_div_assoc] at hh
  exact (div_eq_iff (ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x)))).mp hh

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularRatio_aut_translate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio o (φ.vertex x) =
      G.modularRatio o (φ.vertex o) * G.modularRatio o x := by
  rw [←G.modularRatio_cocycle hc hl o (φ.vertex o) (φ.vertex x),Aut.modularRatio]

def modularCharacter (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (o : V) :
    G.Aut →* ℝ where
  toFun φ := G.modularRatio o (φ.vertex o)
  map_one' := G.modularRatio_self o
  map_mul' φ ψ := by
    change G.modularRatio o (φ.vertex (ψ.vertex o)) = _
    exact G.modularRatio_aut_translate hc hl o (ψ.vertex o) φ

@[simp] lemma modularCharacter_apply (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (φ : G.Aut) :
    G.modularCharacter hc hl o φ = G.modularRatio o (φ.vertex o) := rfl

def modularCoordinate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : ℝˣ := Units.mk0 (G.modularRatio o x)
      (ne_of_gt (G.modularRatio_pos hc hl o x))

@[simp] lemma modularCoordinate_val (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : (G.modularCoordinate hc hl o x : ℝ) = G.modularRatio o x := rfl

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularLevelGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[instance_reducible] def autEdgeAction : MulAction G.Aut E where
  smul φ e := φ.edge e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance instMulActionAut_1 : MulAction G.Aut E := G.autEdgeAction

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Classification_FaithfulOrbitalModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitalActionGroup (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    Subgroup (G.orbitPower o L ≃g G.orbitPower o L) :=
  ((G.orbitPowerHom o L).comp Λ.subtype).range

def orbitalActionMap (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    Λ →* G.orbitalActionGroup o L Λ :=
  ((G.orbitPowerHom o L).comp Λ.subtype).rangeRestrict

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_LevelContactGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def exteriorCluster (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set V :=
  G.cluster (ω∩G.inducedEdges {v | j ≤ π v}) o

def levelContacts (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set V :=
  G.exteriorCluster π j o ω∩{v | π v=j}

def contactDrop (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set E :=
  {e | ∃ v∈G.levelContacts π j o ω, ∃ w, π w<j ∧ G.ends e=s(v,w)}

def minimumLevel (π : V → ℤ) (o : V) (j : ℤ) : Set (Set E) :=
  G.hitEvent o {v | π v=j}\G.hitEvent o {v | π v<j}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_LevelContactMeasurability
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

namespace BernoulliProduct
variable {E : Type*}
lemma measurable_inter_block (X : Set E) :
    @Measurable (Set E) (Set E) (blockSigma X) inferInstance (fun ω => ω∩X) := by
  have hh := measurable_forceOn_block Xᶜ (∅ : Set E)
  rw [compl_compl] at hh
  have he : forceOn Xᶜ (∅ : Set E)=(fun ω : Set E => ω∩X) := by
    unfold forceOn
    funext configuration
    apply Set.ext
    intro edge
    rw [Set.mem_inter_iff]
    simp only [Membership.mem, Set.Mem]
    split_ifs with hedge
    · exact ⟨False.elim, fun hmem => hedge hmem.2⟩
    · exact ⟨fun hmem => ⟨hmem, not_not.mp hedge⟩, And.left⟩
  rw [he] at hh
  exact hh
end BernoulliProduct

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

variable [Countable V] [Countable E]

def fewContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | ∃ U : Finset V, G.levelContacts π j o ω=(U : Set V) ∧ U.Nonempty ∧ U.card<k}

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_RestrictedSeed
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def restrictedSeed (A T : Set V) (S : Set E) : Set (Set E) :=
  {ω | ω∩S∈G.seedHitEvent A T}

lemma measurableSet_restrictedSeed [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet[blockSigma S] (G.restrictedSeed A T S) :=
  (G.measurableSet_seedHitEvent A T).preimage (measurable_inter_block S)

lemma restrictedSeed_measurable [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet (G.restrictedSeed A T S) :=
  (blockSigma_le S) _ (G.measurableSet_restrictedSeed A T S)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph

variable {V : Type*}

def timeCenter (T : ℝ) (v : Site) : ℝ := ((v.1 : ℝ)+v.2)*T
def heightCenter (T : ℝ) (v : Site) : ℝ := ((v.1 : ℝ)-v.2)*T/4
def normalized (t z : V → ℝ) (T : ℝ) : V → Point := fun x => (t x/T,4*z x/T)
def localTime (t : V → ℝ) (T : ℝ) (v : Site) : V → ℝ := fun x => t x-timeCenter T v
def localHeight (z : V → ℝ) (T : ℝ) (v : Site) : V → ℝ := fun x => z x-heightCenter T v
def sign (b : Bool) : ℝ := if b then 1 else -1

def mark (t z : V → ℝ) (T ρ : ℝ) (v : Site) : Set V :=
  {x | 0≤localTime t T v x ∧ localTime t T v x≤ρ ∧ |localHeight z T v x|≤210}

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteOpenWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def HasFiniteOpenWitness (A : Set (Set E)) : Prop :=
  ∀ ω ∈ A, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ s ∈ A

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_MoveWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def boxMove (t z : V → ℝ) (m : ℕ) (precision radius : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.vertexBall y m, ∃ b, ∃ w : (G.openGraph ω).Walk a b,
    (∀ x∈w.support, |t x-t y| ≤ radius ∧ |z x-z y| ≤ radius) ∧
    |t b-(t y+1)|≤precision ∧ |z b-(z y+s)|≤precision}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_MoveExit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def axisExit (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) : Set (Set E) :=
  G.restrictedSeed A {x | L≤Corridor.sign b*u x ∧ Corridor.sign b*u x≤L+D ∧
    |u x|≤L+D ∧ |v x|≤W} (G.inducedEdges {x | |u x|≤L+D ∧ |v x|≤W})

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_StripMoves
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stripPercolates (v : V → ℝ) (W : ℝ) : Set (Set E) :=
  {ω | ω∩G.inducedEdges {x | |v x|≤W}∈G.percolates}

def someStripPercolates (v : V → ℝ) : Set (Set E) :=
  ⋃ n : ℕ, G.stripPercolates v n

def seedStripInfinite (v : V → ℝ) (A : Set V) (W : ℝ) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a).Infinite}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterTail (o : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster ω o ∧ n ≤ K.ncard}

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripCompactness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def seedDomainTail (A S : Set V) (n : ℕ) : Set (Set E) :=
  ⋃ a∈A, (fun ω : Set E => ω∩G.inducedEdges S) ⁻¹' G.clusterTail a n

def seedDomainInfinite (A S : Set V) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster (ω∩G.inducedEdges S) a).Infinite}

def prefix_inside_domain {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n)
    (S : Set V) (hS : ∀ i, p.vertex i∈S) :
    G.RayPrefix (ω∩G.inducedEdges S) a n := {
  vertex := p.vertex, start := p.start, injective := p.injective, ball := p.ball
  adjacent := fun i => (G.open_induced_adj S ω _ _).mpr
    ⟨p.adjacent i,hS i.castSucc,hS i.succ⟩ }

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_MovingStrips
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def parallelCoordinate (u v : V → ℝ) (a b : ℝ) (x : V) : ℝ := a*u x+b*v x
def normalCoordinate (u v : V → ℝ) (a b : ℝ) (x : V) : ℝ := -b*u x+a*v x

def longStripExit (u v : V → ℝ) (A : Set V) (W L a b : ℝ) : Set (Set E) :=
  G.restrictedSeed A
    ({x | |normalCoordinate u v a b x|≤W}∩{x | L≤|parallelCoordinate u v a b x|})
    (G.inducedEdges {x | |normalCoordinate u v a b x|≤W})

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_AdaptiveReveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct

structure RevealPartition (E I : Type*) [Fintype I] where
  block : I → Set E
  cell : I → Set (Set E)
  measurable : ∀ i, MeasurableSet[blockSigma (block i)] (cell i)
  disjoint : Pairwise (Disjoint on cell)
  cover : (⋃ i, cell i)=Set.univ

namespace RevealPartition
variable {E I : Type*} [Fintype I] (P : RevealPartition E I)

lemma exists_cell (σ : Set E) : ∃ i, σ∈P.cell i := by
  have h : σ∈⋃ i, P.cell i := by rw [P.cover]; trivial
  exact Set.mem_iUnion.mp h

lemma cell_unique {σ : Set E} {i j : I} (hi : σ∈P.cell i) (hj : σ∈P.cell j) : i=j := by
  by_contra h
  exact Set.disjoint_left.mp (P.disjoint h) hi hj

@[instance_reducible] def historySigma : MeasurableSpace (Set E) where
  MeasurableSet' A := ∀ i, MeasurableSet[blockSigma (P.block i)] (A∩P.cell i)
  measurableSet_empty := by intro i; simp
  measurableSet_compl := by
    intro A hA i
    have he : Aᶜ∩P.cell i=P.cell i\(A∩P.cell i) := by ext σ; simp; tauto
    rw [he]
    exact (P.measurable i).diff (hA i)
  measurableSet_iUnion := by
    intro A hA i
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (fun n => hA n i)

def probability (q : E → unitInterval) (A : Set (Set E)) (σ : Set E) : ℝ≥0∞ :=
  ∑ i, (P.cell i).indicator (blockProbability q (P.block i) A) σ

def enlarge (T : I → Set E) (hT : ∀ i, P.block i⊆T i) : RevealPartition E I where
  block := T
  cell := P.cell
  measurable i := (by
    have hmono : blockSigma (P.block i) ≤ blockSigma (T i) :=
      iSup₂_mono' (fun e he => ⟨e,hT i he,le_rfl⟩)
    exact hmono _ (P.measurable i))
  disjoint := P.disjoint
  cover := P.cover

def decide {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (d : I → Set E → J)
    (hd : ∀ i, @Measurable (Set E) J (blockSigma (P.block i)) inferInstance (d i)) :
    RevealPartition E (I×J) where
  block ij := P.block ij.1
  cell ij := P.cell ij.1∩(d ij.1 ⁻¹' {ij.2})
  measurable ij := (P.measurable ij.1).inter (hd ij.1 (MeasurableSet.singleton _))
  disjoint := by
    intro ij kl hne
    apply Set.disjoint_left.mpr
    intro σ hσ hτ
    have hi : ij.1=kl.1 := P.cell_unique hσ.1 hτ.1
    have hj : ij.2=kl.2 := by
      have ht : d kl.1 σ=kl.2 := hτ.2
      rw [← hi] at ht
      exact hσ.2.symm.trans ht
    exact hne (Prod.ext hi hj)
  cover := by
    apply Set.eq_univ_of_forall
    intro σ
    obtain ⟨i,hi⟩ := P.exists_cell σ
    exact Set.mem_iUnion.mpr ⟨(i,d i σ),hi,rfl⟩

end RevealPartition
end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_DecisionHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct

def DecisionCode : ℕ → Type
  | 0 => Unit
  | n+1 => DecisionCode n×Bool

instance instFintypeDecisionCode (n : ℕ) : Fintype (DecisionCode n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (DecisionCode n×Bool))

structure DecisionRule (E S : Type*) where
  initial : S
  block : S → Set E
  further : ℕ → S → Set E
  contained : ∀ n s, block s⊆further n s
  active : ℕ → S → Prop
  accept : ℕ → S → Set (Set E)
  measurable : ∀ n s, MeasurableSet[blockSigma (further n s)] (accept n s)
  update : ℕ → S → Bool → S
  block_update : ∀ n s b, block (update n s b)=further n s

namespace DecisionRule
variable {E S : Type*} (D : DecisionRule E S)

def state : (n : ℕ) → DecisionCode n → S
  | 0,_ => D.initial
  | n+1,(w,b) => D.update n (state n w) b

def partitionWithBlock : (n : ℕ) →
    {P : RevealPartition E (DecisionCode n) // ∀ w, P.block w=D.block (D.state n w)}
  | 0 => ⟨{
      block := fun _ => D.block D.initial
      cell := fun _ => Set.univ
      measurable := fun _ => MeasurableSet.univ
      disjoint := by intro i j hne; have he : i=j := @Subsingleton.elim Unit _ i j; exact (hne he).elim
      cover := Set.eq_univ_of_forall (fun _ => Set.mem_iUnion.mpr ⟨(),Set.mem_univ _⟩) },
      fun _ => rfl⟩
  | n+1 => by
      let P := (partitionWithBlock n).val
      have hP := (partitionWithBlock n).property
      let Q := P.enlarge (fun w => D.further n (D.state n w)) (by
        intro w
        rw [hP w]
        exact D.contained n (D.state n w))
      let T := Q.decide (fun w ω => if ω∈D.accept n (D.state n w) then true else false) (by
        intro w
        exact Measurable.ite (D.measurable n (D.state n w)) measurable_const measurable_const)
      refine ⟨T,?_⟩
      intro w
      change D.further n (D.state n w.1)=D.block (D.update n (D.state n w.1) w.2)
      exact (D.block_update n _ _).symm

def partition (n : ℕ) : RevealPartition E (DecisionCode n) :=
  (D.partitionWithBlock n).val

def failure (n : ℕ) : Set (Set E) := ⋃ w : DecisionCode n,
  (D.partition n).cell w∩{ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)}

def codeOf : (n : ℕ) → Set E → DecisionCode n
  | 0,_ => ()
  | n+1,ω => (codeOf n ω,if ω∈D.accept n (D.state n (codeOf n ω)) then true else false)

end DecisionRule
end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BalancedCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Boundary

def balancedPermutation {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) : Equiv.Perm E :=
  Equiv.ofFiberEquiv (fun v => Fintype.equivOfCardEq (hb v))

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_SquareBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

abbrev Grid := ℤ×ℤ
abbrev Dir := Fin 4
abbrev Edge := Grid×Dir

def step : Dir → Grid := ![(1,0),(0,1),(-1,0),(0,-1)]
def leftOffset : Dir → Grid := ![(0,0),(-1,0),(-1,-1),(0,-1)]
def rightOffset : Dir → Grid := ![(0,-1),(0,0),(-1,0),(-1,-1)]
def tail (e : Edge) : Grid := e.1
def head (e : Edge) : Grid := e.1+step e.2
def leftSite (e : Edge) : Grid := e.1+leftOffset e.2
def rightSite (e : Edge) : Grid := e.1+rightOffset e.2

def squareBoundary (S : Set Grid) : Set Edge :=
  {e | leftSite e∈S ∧ rightSite e∉S}

def outgoingEquiv (S : Set Grid) (v : Grid) :
    {e : squareBoundary S // tail e=v} ≃ {d : Dir // (v,d)∈squareBoundary S} where
  toFun e := ⟨e.1.1.2,by
    have h := e.1.2
    have hv := e.2
    change e.1.1.1=v at hv
    change leftSite (e.1.1.1,e.1.1.2)∈S ∧ rightSite (e.1.1.1,e.1.1.2)∉S at h
    rwa [hv] at h⟩
  invFun d := ⟨⟨(v,d.1),d.2⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.2.symm rfl
  right_inv d := rfl

def incomingEquiv (S : Set Grid) (v : Grid) :
    {e : squareBoundary S // head e=v} ≃
      {d : Dir // (v-step d,d)∈squareBoundary S} where
  toFun e := ⟨e.1.1.2,by
    have hv : e.1.1.1=v-step e.1.1.2 := eq_sub_iff_add_eq.mpr e.2
    have h := e.1.2
    change leftSite (e.1.1.1,e.1.1.2)∈S ∧ rightSite (e.1.1.1,e.1.1.2)∉S at h
    rwa [hv] at h⟩
  invFun d := ⟨⟨(v-step d.1,d.1),d.2⟩,sub_add_cancel _ _⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    change (v-step e.1.1.2,e.1.1.2)=e.1.1
    exact Prod.ext (eq_sub_iff_add_eq.mpr e.2).symm rfl
  right_inv d := rfl

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ContourSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

def forwardDir (d : Dir) : Prop := d=1 ∨ d=2

def forwardIndices (e : ℕ → Edge) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => forwardDir (e i).2)

def outsideSites (e : ℕ → Edge) (n : ℕ) : Finset Grid :=
  (forwardIndices e n).image (fun i => rightSite (e i))

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ContourWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

def wordDir {n : ℕ} (w : Fin n → Dir) (i : ℕ) : Dir :=
  if h : i<n then w ⟨i,h⟩ else if h₀ : 0<n then w ⟨0,h₀⟩ else 0

def wordEdge {n : ℕ} (p : Grid) (w : Fin n → Dir) (i : ℕ) : Edge :=
  (p+∑ j∈Finset.range i, step (wordDir w j),wordDir w i)

def wordValid {n : ℕ} (p : Grid) (w : Fin n → Dir) : Prop :=
  wordEdge p w n=wordEdge p w 0 ∧ Set.InjOn (wordEdge p w) (Set.Iio n)

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ContourProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

namespace Boundary

def wordFailure {Ω : Type*} (B : Set Ω) (F : Grid → Set Ω)
    {n : ℕ} (w : Fin n → Dir) : Set Ω :=
  if wordValid (0,1) w then B∩⋂ z∈outsideSites (wordEdge (0,1) w) n, F z else ∅

end Boundary
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SlotContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.Boundary

def gridSlot (v : Grid) : ℕ := Nat.pair v.1.toNat v.2.toNat

def quadrant (v : Grid) : Prop := 0≤v.1 ∧ 0≤v.2

def gridFailure {Ω : Type*} (F : ℕ → Set Ω) (v : Grid) : Set Ω :=
  if quadrant v then F (gridSlot v) else ∅

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_LatticeGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open Boundary

def slotSite (n : ℕ) : Site := ((Nat.unpair n).1,(Nat.unpair n).2)

def incoming (n : ℕ) (S : Finset Site) : Option Edge :=
  if (slotSite n-(1,0))∈S then some (slotSite n-(1,0),true)
  else if (slotSite n-(0,1))∈S then some (slotSite n-(0,1),false) else none

structure GrowthState where
  good : Finset Site
  seen : Finset Edge

def GrowthState.initial : GrowthState := ⟨{(0,0)},∅⟩

def GrowthState.advance (n : ℕ) (S : GrowthState) (b : Bool) : GrowthState where
  good := if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good
  seen := S.seen∪(incoming n S.good).toFinset

lemma GrowthState.seen_mono (n : ℕ) (S : GrowthState) (b : Bool) :
    S.seen⊆(S.advance n b).seen := Finset.subset_union_left

def GrowthState.Valid (n : ℕ) (S : GrowthState) : Prop :=
  (0,0)∈S.good ∧
  (∀ v∈S.good, quadrant v ∧ (v=(0,0) ∨ gridSlot v<n)) ∧
  (∀ e∈S.seen, source e∈S.good ∧ gridSlot (target e)<n)

def GrowthState.Covered (S : GrowthState) : Prop :=
  ∀ v∈S.good, v=(0,0) ∨ ∃ e∈S.seen, target e=v

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_PinnedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def predictionFailure (q : E → unitInterval) (F : Set E)
    (A C D : Set (Set E)) (δ : ℝ) : Set (Set E) :=
  Aᶜ ∪ (A∩{σ | (blockProbability q F C σ).toReal<1-δ}) ∪
    (A∩{σ | (blockProbability q F D σ).toReal<1-δ})

lemma measurableSet_predictionFailure (q : E → unitInterval) (F : Set E)
    (A C D : Set (Set E)) (hA : MeasurableSet[blockSigma F] A)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (δ : ℝ) :
    MeasurableSet[blockSigma F] (predictionFailure q F A C D δ) := by
  exact (hA.compl.union (hA.inter (measurableSet_lt
    (measurable_blockProbability q F C hC).ennreal_toReal measurable_const))).union
    (hA.inter (measurableSet_lt
      (measurable_blockProbability q F D hD).ennreal_toReal measurable_const))

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_GrowthProcess
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

structure Scheme (V E : Type*) where
  graph : BondGraph V E
  coordinate : V → Point
  j : ℝ
  h : ℝ
  seed : Set V
  mark : Site → Set V
  parameter : E → unitInterval
  delta : ℝ

namespace Scheme
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def hit (v : Site) (R : Set E) : Set (Set E) := P.graph.restrictedSeed P.seed (P.mark v) R

end Scheme
end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteSeedTree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ballRank (o v : V) : ℕ :=
  if h : ∃ n, v∈G.vertexBall o n then Nat.find h else 0

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ContactSelection
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

variable [Countable V] [Countable E]
def manyContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | (G.levelContacts π j o ω).Nonempty}\G.fewContacts π j o k

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SelectedFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

def selectedEvent (d : Set E → I) (A : I → Set (Set E)) : Set (Set E) :=
  {ω | ω∈A (d ω)}

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SourceGraph
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def withSource (A : Set V) : BondGraph (Option V) (E⊕A) where
  ends e := match e with
    | Sum.inl b => Sym2.map Option.some (G.ends b)
    | Sum.inr a => s(none,some a.val)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def corridorRelay (t z : V → ℝ) (σ e ρ : ℝ) (L i : ℕ) : Set V :=
  if i=0 then relayMark t z 0 σ ρ
  else if i ≤ L then relayRegion t z σ e i else relayMark t z (L+1/2) σ ρ

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_RelayProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation
variable {Ω : Type*} [MeasurableSpace Ω]

namespace BernoulliProduct
variable {E : Type*}

def twoPredictions (q : E → unitInterval) (S : Set E) (C D : Set (Set E))
    (δ : ℝ) : Set (Set E) :=
  {σ | 1-δ ≤ (blockProbability q S C σ).toReal ∧
    1-δ ≤ (blockProbability q S D σ).toReal}

end BernoulliProduct
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_CoordinateScheme
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

structure CoordinateData (V E : Type*) where
  graph : BondGraph V E
  origin : V
  time : V → ℝ
  height : V → ℝ
  J : ℝ
  L : ℕ
  R : ℕ
  m : ℕ
  D : ℕ
  k : ℕ
  M : ℕ
  VM : ℕ
  e : ℝ
  rho : ℝ
  kappa : ℝ
  eta : ℝ
  delta : ℝ
  contour : ℝ
  pc : unitInterval
  p : unitInterval

namespace CoordinateData
variable {V E : Type*} (C : CoordinateData V E)

def T : ℝ := C.L+1/2

def scheme : Scheme V E where
  graph := C.graph
  coordinate := normalized C.time C.height C.T
  j := C.J/C.T
  h := 2520/C.T
  seed := C.graph.vertexBall C.origin C.m
  mark := Corridor.mark C.time C.height C.T C.rho
  parameter := fun _ => C.p
  delta := C.delta

structure Bounds : Prop where
  connected : C.graph.fullGraph.Connected
  locallyFinite : C.graph.LocallyFinite
  time_origin : C.time C.origin=0
  height_origin : C.height C.origin=0
  time_step : ∀ ⦃u v⦄, C.graph.fullGraph.Adj u v → |C.time u-C.time v|≤C.rho
  height_step : ∀ ⦃u v⦄, C.graph.fullGraph.Adj u v → |C.height u-C.height v|≤C.rho
  J_lower : 26200<C.J
  L_lower : 10*(C.J+210)<C.L
  e_pos : 0<C.e
  rho_nonneg : 0≤C.rho
  e_small : (C.L+3)*C.e<1/100
  rho_small : (C.R+C.m+1)*C.rho<C.e/10
  R_gt : C.m<C.R
  pc_pos : 0<(C.pc : ℝ)
  pc_lt : (C.pc : ℝ)<1
  p_lower : (C.pc : ℝ)/2≤C.p
  p_upper : (C.p : ℝ)≤C.pc
  degree : ∀ v, (C.graph.incidentEdges {v}).ncard≤C.D
  M_pos : 0<C.M
  M_bound : ∀ v, (C.graph.vertexBall v (4*C.m+2)).ncard≤C.M
  VM_bound : ∀ v, (C.graph.vertexBall v C.m).ncard≤C.VM
  kappa_pos : 0<C.kappa
  kappa_le : C.kappa≤1
  eta_nonneg : 0≤C.eta
  eta_small : C.eta≤C.kappa*(C.kappa/4)/(4*(Real.log (4/C.kappa)+1))
  k_large : C.M*⌈Real.log (4/C.kappa)/((C.pc : ℝ)/2)^(C.m+1+C.VM)⌉₊≤C.k
  R_large : 4/(C.kappa*(1-(C.pc : ℝ))^(C.D*C.k))<(C.R : ℝ)-C.m
  delta_pos : 0<C.delta
  root_error : 2*(C.eta+C.L*C.kappa)<C.delta
  contour_nonneg : 0≤C.contour
  contour_small : 8*C.contour<1
  test_error : C.delta+2*((C.L+1)*C.kappa)/C.delta≤C.contour^4

end CoordinateData
end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorScaleChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Classical

namespace CriticalPercolation.Corridor.ScaleChoice

def J : ℝ := 30000
def L : ℕ := 1000000

end CriticalPercolation.Corridor.ScaleChoice
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseExit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ellipseExit (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) : Set (Set E) :=
  G.restrictedSeed A {x | ‖Psi x-(c : ℂ)‖≤2*zeta ∧ ‖Psi x‖≤1+zeta}
    (G.inducedEdges {x | ‖Psi x‖≤1+zeta})

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open LinearMap

namespace CriticalPercolation.EllipseLinear

def det (a b c d : ℝ) : ℝ := a*d-b*c

def time (a b c d x y : ℝ) : ℝ := ((d-b)*x+(a-c)*y)/det a b c d

def height (a b c d x y : ℝ) : ℝ := ((d+b)*x-(c+a)*y)/det a b c d

end CriticalPercolation.EllipseLinear
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_EllipseMoves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ellipseTime (Psi : V → ℂ) (c d : Circle) (x : V) : ℝ :=
  EllipseLinear.time (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im (Psi x).re (Psi x).im

def ellipseHeight (Psi : V → ℂ) (c d : Circle) (x : V) : ℝ :=
  EllipseLinear.height (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im (Psi x).re (Psi x).im

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseSeed
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def seedInfiniteEvent (A : Set V) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster ω a).Infinite}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

def diskRadius (W U : ℝ) (p : ℝ×ℝ) : ℝ := W+(U-W)*p.1

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stripTime (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (x : V) : ℝ :=
  Corridor.sign a*u x/U+Corridor.sign b*v x/Q

def stripHeight (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (x : V) : ℝ :=
  Corridor.sign a*u x/U-Corridor.sign b*v x/Q

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryInterpolation
open scoped Classical

def midpoint (l r : ℕ) : ℕ := (l+r)/2

def bisect (l r : ℕ) (side : Bool) : ℕ × ℕ :=
  if r ≤ l+1 then (l,r) else if side then (midpoint l r,r) else (l,midpoint l r)

def terminal (l r : ℕ) : List Bool → ℕ × ℕ
  | [] => (l,r)
  | b::bs => terminal (bisect l r b).1 (bisect l r b).2 bs

end CriticalPercolation.BinaryInterpolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SearchTree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation

inductive SearchTree (E R : Type*) where
  | done (r : R)
  | ask (e : E) (left right : SearchTree E R)

namespace LazyDFS
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

abbrev Dart (V E : Type*) := V × E × V

structure State (V E : Type*) where
  reached : Finset V
  read : Finset E

def State.closed (s : State V E) (e : E) : State V E := ⟨s.reached,insert e s.read⟩
def State.opened (s : State V E) (e : E) (v : V) : State V E :=
  ⟨insert v s.reached,insert e s.read⟩

def push (G : BondGraph V E) (order : List (Dart V E)) (v : V) : List (Dart V E) :=
  order.filter fun d => d.1 = v ∧ G.ends d.2.1 = s(d.1,d.2.2)

noncomputable def compile (G : BondGraph V E) (order : List (Dart V E)) (B : Set V) :
    ℕ → State V E → List (Dart V E) → SearchTree E (State V E)
  | 0, st, _ => .done st
  | n+1, st, stack =>
    if ∃ v ∈ st.reached, v ∈ B then .done st else
    match stack with
    | [] => .done st
    | d :: rest =>
      if d.2.2 ∈ st.reached ∨ d.2.1 ∈ st.read ∨ d.1 ∉ st.reached ∨
        G.ends d.2.1 ≠ s(d.1,d.2.2) then compile G order B n st rest else
      .ask d.2.1 (compile G order B n (st.closed d.2.1) rest)
        (compile G order B n (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest))

variable [Fintype V]

def rank (order : List (Dart V E)) (st : State V E) (stack : List (Dart V E)) : ℕ :=
  (Fintype.card V - st.reached.card)*(order.length+1)+stack.length

end LazyDFS
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Initial
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

noncomputable def initial (w : V) : State V E := ⟨{w},∅⟩

variable [Fintype V]

noncomputable def search (G : BondGraph V E) (order : List (Dart V E)) (w : V) (B : Set V) :
    SearchTree E (State V E) :=
  compile G order B (rank order (initial w) (push G order w)) (initial w) (push G order w)

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterObject
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

abbrev ClusterObject (V E : Type*) := Set V × Set E

def clusterObject (ω : Set E) (S : Set V) : ClusterObject V E :=
  (roots (G.openGraph ω) S, ω ∩ G.incidentEdges (roots (G.openGraph ω) S))

def eraseVertices (ω : Set E) (U : Set V) : Set E := ω \ G.incidentEdges U

lemma clusterObject_eq_of_incident {S : Set V} {C : ClusterObject V E} {ω ω' : Set E}
    (hC : G.clusterObject ω S = C)
    (hω : ∀ e ∈ G.incidentEdges C.1, e ∈ ω ↔ e ∈ ω') :
    G.clusterObject ω' S = C := by
  have hr : roots (G.openGraph ω) S = C.1 := congrArg Prod.fst hC
  have hr' := G.roots_eq_of_incident hr hω
  apply Prod.ext hr'
  change ω' ∩ G.incidentEdges (roots (G.openGraph ω') S) = C.2
  have he : ω ∩ G.incidentEdges (roots (G.openGraph ω) S) = C.2 := congrArg Prod.snd hC
  rw [hr] at he
  rw [hr', ← he]
  ext e
  constructor
  · intro hh
    exact ⟨(hω e hh.2).mpr hh.1, hh.2⟩
  · intro hh
    exact ⟨(hω e hh.2).mp hh.1, hh.2⟩

lemma dependsOn_exact_clusterObject (S : Set V) (C : ClusterObject V E) :
    DependsOn (fun ω : Set E => G.clusterObject ω S = C) (G.incidentEdges C.1) := by
  intro ω ω' hω
  apply propext
  constructor
  · exact fun h => G.clusterObject_eq_of_incident h (fun e he => (hω e he).to_iff)
  · exact fun h => G.clusterObject_eq_of_incident h (fun e he => (hω e he).symm.to_iff)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ObjectKernel
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def objectKernel (w : E → Prop → ℝ) (S : Set V)
    (C D : ClusterObject V E) : ℝ :=
  distribution w (fun ω => G.clusterObject (G.eraseVertices ω C.1) S) D

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ObjectAvoidMass
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def objectAvoidMass (w : E → Prop → ℝ) (A B : Set V)
    (C : ClusterObject V E) : ℝ :=
  if Disjoint C.1 B then distribution w (fun ω => G.clusterObject ω A) C else 0

noncomputable def objectAvoidTotal (w : E → Prop → ℝ) (A B : Set V) : ℝ :=
  expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then 1 else 0)

noncomputable def objectAvoidLaw (w : E → Prop → ℝ) (A B : Set V)
    (C : ClusterObject V E) : ℝ := G.objectAvoidMass w A B C/G.objectAvoidTotal w A B

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_IsolateThree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

def isolateThree (a s t : V) (ω : Set E) : Prop :=
  ¬(G.openGraph ω).Reachable a s ∧ ¬(G.openGraph ω).Reachable a t

def separateThree (a s t : V) (ω : Set E) : Prop :=
  G.isolateThree a s t ω ∧ ¬(G.openGraph ω).Reachable s t

def joinedPair (a s t : V) (ω : Set E) : Prop :=
  G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable s t

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_WiredEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

def wiredEvent (a s t : V) (ω : Set E) : Prop :=
  ((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EraseBond
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

noncomputable def eraseBond (f : E) (o : V) : BondGraph V E :=
  ⟨Function.update G.ends f s(o,o)⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Connects
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

def connects (a t : V) (ω : Set E) : Prop := (G.openGraph ω).Reachable a t

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_MapVertices
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E U : Type*} (G : BondGraph V E)

def mapVertices (f : V → U) : BondGraph U E := ⟨Sym2.map f ∘ G.ends⟩

open scoped Classical

noncomputable def collapseTarget (B : Set V) (v : V) : Option V :=
  if v ∈ B then none else some v
noncomputable def wireTargets (B : Set V) : BondGraph (Option V) E :=
  G.mapVertices (collapseTarget B)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClosedFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def contactScore (T : SearchTree E R) (p : ℝ) (C : Set E)
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : E → Prop) : ℝ :=
  match T with
  | .done _ => 0
  | .ask e l r => (if e ∈ C then p*delta w F e else 0) +
      if ω e then r.contactScore p C F (pin w e True) ω
      else l.contactScore p C F (pin w e False) ω

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_QueryDelta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def queryDelta (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r => if e = f then delta w F f else
      if ω f then r.queryDelta F (pin w f True) ω e
      else l.queryDelta F (pin w f False) ω e

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SequentialExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

structure Exposure (E A B : Type*) where
  record : (E → A) → B
  domain : B → Set E
  bits : B → E → A
  atom : ∀ b, DependsOn (fun ω => record ω = b) (domain b)
  exact : ∀ ω e, e ∈ domain (record ω) → bits (record ω) e = ω e

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def incidenceExposure (G : BondGraph V E) (S : Set V) :
    Exposure E Prop (ClusterObject V E) where
  record := fun ω => G.clusterObject ω S
  domain := fun C => G.incidentEdges C.1
  bits := Prod.snd
  atom := G.dependsOn_exact_clusterObject S
  exact := by
    intro ω e he
    apply propext
    change ω e ∧ e ∈ G.incidentEdges (G.clusterObject ω S).1 ↔ ω e
    exact ⟨fun h => h.1,fun h => ⟨h,he⟩⟩

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def scheduledContact (order : List (LazyDFS.Dart V E))
    (B : Set V) (a : V) (p : ℝ) (w : E → Prop → ℝ)
    (C : ClusterObject V E) (ω : E → Prop) : ℝ :=
  if a ∈ C.1 then 1 else
    (LazyDFS.search G order a B).contactScore p (G.cutEdges C.1)
      (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*}

def anchorSet (S : Set V) (a : ℕ → V) (n : ℕ) : Set V :=
  S ∪ a '' {i | i<n}

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

noncomputable def contactWeight (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (e : E) : ℝ :=
  if e ∈ G.cutEdges O then p*(LazyDFS.search G order a B).queryDelta
    (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω e else 0

noncomputable def contactKernel (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) : ℝ :=
  if a ∈ C.1 then if mark = none then 1 else 0 else
    match mark with
    | none => 0
    | some e => G.contactWeight order B C.1 a p w ω e /
        prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryLaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

universe uE

def History (E : Type uE) : ℕ → Type uE
  | 0 => PUnit
  | n+1 => History E n × Bool × Option E

instance historyFintype {E : Type*} [Fintype E] : (n : ℕ) → Fintype (History E n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
    letI := historyFintype (E := E) n
    exact inferInstanceAs (Fintype (History E n × Bool × Option E))

def interval {E : Type*} (d : ℕ) : (n : ℕ) → History E n → ℕ × ℕ
  | 0, _ => (0,d)
  | n+1, h => bisect (interval d n h.1).1 (interval d n h.1).2 h.2.1

def nextIndex {E : Type*} (d : ℕ) (n : ℕ) (h : History E n) : ℕ :=
  if (interval d n h).2 ≤ (interval d n h).1+1 then (interval d n h).1
    else midpoint (interval d n h).1 (interval d n h).2

def anchors {V E : Type*} (d : ℕ) (x : ℕ → V) : (n : ℕ) → History E n → List (V × Bool)
  | 0, _ => [(x 0,true),(x d,false)]
  | n+1, h => anchors d x n h.1 ++ [(x (nextIndex d n h.1),h.2.1)]

def anchorSet {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) : Set V :=
  {v | ∃ b, (v,b) ∈ anchors d x n h}

noncomputable def firstIndex (P : ℕ → Prop) : ℕ :=
  if h : ∃ j, P j then Nat.find h else 0

variable {V E : Type*} (G : BondGraph V E)

def parentPredicate (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) (j : ℕ) : Prop :=
  ∃ z, L[j]? = some z ∧ match m with
    | none => (G.openGraph ω).Reachable a z.1
    | some e => ∃ v ∈ G.ends e, (G.openGraph ω).Reachable z.1 v

noncomputable def parent (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) : ℕ :=
  firstIndex (parentPredicate G L a ω m)

noncomputable def side (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) : Bool :=
  ((L[parent G L a ω m]?).getD (a,true)).2

section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

noncomputable def density : (n : ℕ) → History E n → (E → Prop) → ℝ
  | 0, _, ω => r₀ ω
  | n+1, h, ω =>
    if side G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 = h.2.1 then
      density n h.1 ω * G.contactKernel order (anchorSet d x n h.1)
        (x (nextIndex d n h.1)) p w (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2
      else 0

end Density

section Seed
variable [Fintype V] [Fintype E]

def endpointEvent (u v : V) (s : ℕ) (ω : Set E) : Prop :=
  ¬ (G.openGraph ω).Reachable u v ∧
    s ≤ (G.cluster ω u).toFinset.card ∧ s ≤ (G.cluster ω v).toFinset.card

noncomputable def seed (w : E → Prop → ℝ) (u v : V) (s : ℕ) (ω : E → Prop) : ℝ :=
  (prob w (endpointEvent G u v s))⁻¹ * if endpointEvent G u v s ω then 1 else 0

end Seed

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinarySupport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*} (G : BondGraph V E)

def Consistent (L : List (V × Bool)) (ω : Set E) : Prop :=
  ∀ z ∈ L, ∀ t ∈ L, (G.openGraph ω).Reachable z.1 t.1 → z.2=t.2

def sideWord {E : Type*} : (n : ℕ) → History E n → List Bool
  | 0, _ => []
  | n+1, h => sideWord n h.1 ++ [h.2.1]

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_AncestryForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest

structure Forest where
  parent : ℕ → ℕ
  parent_lt : ∀ n, 2 ≤ n → parent n < n

namespace Forest
variable (F : Forest)

def lineage (F : Forest) (n : ℕ) : List ℕ :=
  if _h : n < 2 then [n] else n :: F.lineage (F.parent n)
termination_by n
decreasing_by exact F.parent_lt n (by omega)

end Forest
end CriticalPercolation.InterpolationForest

namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

def active (u v : ℕ) : Finset ℕ :=
  ((F.lineage u ++ F.lineage v).toFinset).filter (fun i => 2 ≤ i)

end CriticalPercolation.InterpolationForest.Forest
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryForest
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

noncomputable def nodeParent (d : ℕ) (x : ℕ → V) (ω : Set E) :
    (n : ℕ) → History E n → ℕ → ℕ
  | 0, _, i => if i=1 then 1 else 0
  | n+1, h, i => if i=n+2 then
      let j := parent G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2
      if j<n+2 then j else 0
    else nodeParent d x ω n h.1 i

lemma nodeParent_lt (d : ℕ) (x : ℕ → V) (ω : Set E) (n : ℕ) (h : History E n)
    (i : ℕ) (hi : 2 ≤ i) : nodeParent G d x ω n h i < i := by
  induction n with
  | zero => simp only [nodeParent,ite_eq_right (by omega : i≠1)]; omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      simp only [nodeParent,ite_true, if_true]
      split_ifs with hp
      · exact hp
      · omega
    · rw [nodeParent,ite_eq_right he]
      exact ih h.1

noncomputable def historyForest (d : ℕ) (x : ℕ → V) (ω : Set E)
    (n : ℕ) (h : History E n) : Forest :=
  ⟨nodeParent G d x ω n h, nodeParent_lt G d x ω n h⟩

def node (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) : V × Bool :=
  (anchors d x n h)[i]?.getD (x 0,true)

def Canonical (L : List (V × Bool)) (ω : Set E) (i : ℕ) : Prop :=
  ∀ j z t, j < i → L[j]? = some z → L[i]? = some t →
    ¬(G.openGraph ω).Reachable z.1 t.1

noncomputable def owner (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) : ℕ := parent G (anchors d x n h) a ω none

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryMarks
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def nodeMark : (n : ℕ) → History E n → ℕ → Option E
  | 0, _, _ => none
  | n+1, h, i => if i = n+2 then h.2.2 else nodeMark n h.1 i

noncomputable def activeNodes (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) : Finset ℕ :=
  (historyForest G d x ω n h).active (owner G d x n h ω (x (interval d n h).1))
    (owner G d x n h ω (x (interval d n h).2))

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

def sides : (n : ℕ) → History E n → Fin n → Bool
  | 0, _ => Fin.elim0
  | n+1, h => Fin.snoc (sides n h.1) h.2.1

def marks : (n : ℕ) → History E n → Fin n → Option E
  | 0, _ => Fin.elim0
  | n+1, h => Fin.snoc (marks n h.1) h.2.2

def fromWords : (n : ℕ) → (Fin n → Bool) → (Fin n → Option E) → History E n
  | 0, _, _ => PUnit.unit
  | n+1, b, m => (fromWords n (Fin.init b) (Fin.init m),b (Fin.last n),m (Fin.last n))

lemma fromWords_sides_marks (n : ℕ) (h : History E n) :
    fromWords n (sides n h) (marks n h) = h := by
  induction n with
  | zero => cases h; rfl
  | succ n ih =>
    simp only [fromWords,sides,marks,Fin.init_snoc,Fin.snoc_last,ih]
    rfl

lemma sides_fromWords (n : ℕ) (b : Fin n → Bool) (m : Fin n → Option E) :
    sides n (fromWords n b m) = b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [fromWords,sides,ih,Fin.snoc_init_self]

lemma marks_fromWords (n : ℕ) (b : Fin n → Bool) (m : Fin n → Option E) :
    marks n (fromWords n b m) = m := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [fromWords,marks,ih,Fin.snoc_init_self]

def wordsEquiv (n : ℕ) : History E n ≃ (Fin n → Bool) × (Fin n → Option E) where
  toFun h := (sides n h, marks n h)
  invFun h := fromWords n h.1 h.2
  left_inv := fromWords_sides_marks n
  right_inv := fun h => Prod.ext (sides_fromWords n h.1 h.2) (marks_fromWords n h.1 h.2)

def historyPrefix : (n : ℕ) → History E n → (k : ℕ) → History E k
  | 0, _, 0 => PUnit.unit
  | 0, _, k+1 => fromWords (k+1) (fun _ => true) (fun _ => none)
  | n+1, h, k => if he : k = n+1 then he.symm ▸ h else historyPrefix n h.1 k

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClosedPivotWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def prefixScore (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r => (if openPivot F f ω then (1-p)*delta w F f else 0) +
      if e = f then 0 else
        if ω f then r.prefixScore p F (pin w f True) ω e
        else l.prefixScore p F (pin w f False) ω e

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_ReverseGuess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def reverseGuess (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) (e : E) : ℝ :=
  (if openPivot F e ω then (1-p)*T.queryDelta F w ω e else 0) /
    (1+s+T.prefixScore p F w ω e)^2

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_QueryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation

universe u

inductive QueryTree (E : Type u) : Type u where
  | stop : QueryTree E
  | ask (e : E) (left right : QueryTree E) : QueryTree E

namespace QueryTree
variable {E : Type u}

@[reducible] def Leaf : QueryTree E → Type u
  | .stop => PUnit
  | .ask _ left right => Sum left.Leaf right.Leaf

def run : (t : QueryTree E) → (E → Bool) → t.Leaf
  | .stop, _ => PUnit.unit
  | .ask e left right, ω => if ω e then Sum.inr (right.run ω) else Sum.inl (left.run ω)

end QueryTree
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PushMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteEntropy
variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def pushMass (f : X → Y) (P : X → ℝ) (y : Y) : ℝ :=
  ∑ x, if f x = y then P x else 0

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_BitWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

noncomputable def bitWeight (p : ℝ) (_ : E) (b : Bool) : ℝ := if b then p else 1-p

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Node
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
variable {E : Type*}

@[reducible] def Node : QueryTree E → Type
  | .stop => PEmpty
  | .ask _ l r => PUnit ⊕ (l.Node ⊕ r.Node)

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_Uniform01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.Priority

noncomputable def uniform01 : Measure ℝ := volume.restrict (Icc 0 1)

instance instIsProbabilityMeasureRealUniform01 : IsProbabilityMeasure uniform01 := by
  constructor
  simp [uniform01, Real.volume_Icc]

end CriticalPercolation.Priority
open Set MeasureTheory Real
open scoped Interval

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_State
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

structure State (V E : Type*) where
  reached : Finset V
  read : Finset E

noncomputable def eligible (G : BondGraph V E) (st : State V E) (e : E) : Prop :=
  e ∉ st.read ∧ ∃ v ∈ st.reached, v ∈ G.ends e

noncomputable def closed (st : State V E) (e : E) : State V E :=
  ⟨st.reached, insert e st.read⟩

noncomputable def opened (G : BondGraph V E) (st : State V E) (e : E) : State V E :=
  ⟨st.reached ∪ (G.ends e).toFinset, insert e st.read⟩

noncomputable def compile (G : BondGraph V E) : ℕ → State V E → SearchTree E (State V E)
  | 0, st => .done st
  | n+1, st => if h : ∃ e, eligible G st e then
      let e := Classical.choose h
      .ask e (compile G n (closed st e)) (compile G n (opened G st e))
    else .done st

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Initial2
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

noncomputable def initial (S : Finset V) : State V E := ⟨S,∅⟩
noncomputable def search (G : BondGraph V E) (S : Finset V) : SearchTree E (State V E) :=
  compile G (Fintype.card E) (initial S)

noncomputable def pair (G : BondGraph V E) (a b : V) : SearchTree E (State V E) :=
  search G {a,b}

end CriticalPercolation.ExactExposure

namespace CriticalPercolation
namespace SearchTree
variable {E R : Type*}
def bare : SearchTree E R → QueryTree E
  | .done _ => .stop
  | .ask e l r => .ask e l.bare r.bare

end SearchTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClusterUsers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*}

def configuration (ω : E → Bool) : Set E := {e | ω e = true}

def Admissible (G : BondGraph V E) (B : Set V) (a b : V) (ω : E → Bool) (f : E) : Prop :=
  (¬∃ t ∈ B, (G.openGraph (configuration ω)).Reachable a t) ∧
    ∃ u v, G.ends f = s(u,v) ∧ (G.openGraph (configuration ω)).Reachable a u ∧
      (G.openGraph (configuration ω)).Reachable b v

variable [Fintype E]

variable [Fintype V]

noncomputable def markWeight (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Bool) (f : E) : ℝ :=
  if Admissible G B a b ω f then
    p * (LazyDFS.search G order a B).queryDelta
      (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f
  else 0

noncomputable def markCost (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Bool) (f : E) : ℝ :=
  if Admissible G B a b ω f then
    (LazyDFS.search G order a B).prefixScore p
      (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
      (Function.update (configuration ω) f True) f
  else 0

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryDescriptor
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest FiniteEntropy ExactExposure

variable {V E : Type*}

abbrev FixedDescriptor (n : ℕ) := Fin n → Bool × Bool × Bool

noncomputable def descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) : FixedDescriptor n := fun i =>
  (sides n h i, decide (marks n h i ≠ none), decide (i.val+2 ∈ activeNodes G d x n h ω))

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ)

noncomputable def jointMass (z : (E → Bool) × History E n) : ℝ :=
  FiniteProduct.density (QueryTree.bitWeight p) z.1 *
    density G order d x p w (seed G w (x 0) (x d) s) n z.2 (configuration z.1)

noncomputable def descriptorMass (D : FixedDescriptor n) : ℝ :=
  pushMass (fun z : (E → Bool) × History E n => descriptor G d x n z.2 (configuration z.1))
    (jointMass G order d x p w s n) D

noncomputable def fixedMass (D : FixedDescriptor n) (z : (E → Bool) × (Fin n → Option E)) : ℝ :=
  let h := fromWords n (fun i => (D i).1) z.2
  if descriptor G d x n h (configuration z.1) = D then
    jointMass G order d x p w s n (z.1,h) else 0

noncomputable def conditionedMass (D : FixedDescriptor n)
    (z : (E → Bool) × (Fin n → Option E)) : ℝ :=
  fixedMass G order d x p w s n D z / descriptorMass G order d x p w s n D

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryRaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

noncomputable def rawContact (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) : ℝ :=
  if a ∈ C.1 then if mark = none then 1 else 0 else
    match mark with
    | none => 0
    | some e => G.contactWeight order B C.1 a p w ω e

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

def scheduledAnchor (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool) (k : ℕ) : V :=
  x (nextIndex d k (historyPrefix n (fromWords n b (fun _ => (none : Option E))) k))

def scheduledTargets (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool) (k : ℕ) : Set V :=
  anchorSet d x k (historyPrefix n (fromWords n b (fun _ => (none : Option E))) k)

section Products
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

noncomputable def rawProduct : (n : ℕ) → History E n → (E → Prop) → ℝ
  | 0, _, _ => 1
  | n+1, h, ω => rawProduct n h.1 ω *
      G.rawContact order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
        (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2

noncomputable def scheduleWeight (n : ℕ) (b : Fin n → Bool)
    (i : Fin n) (ω : E → Prop) (m : Option E) : ℝ :=
  G.rawContact order (scheduledTargets (E := E) d x n b i.val)
    (scheduledAnchor (E := E) d x n b i.val) p w
    (G.clusterObject ω (scheduledTargets (E := E) d x n b i.val)) ω m

end Products
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_MarkedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]

noncomputable def logContactMass (a : I → X → M → ℝ) (ω : X) : ℝ :=
  ∑ i, Real.log (max 1 (∑ m, a i ω m))

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryConfiguration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation FiniteEntropy ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

noncomputable def constructionCost (c : ℝ) (s n : ℕ) (D : FixedDescriptor n) : ℝ :=
  Real.log ((prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n /
    descriptorMass G order d x p w s n D)

noncomputable section EntropyFinal
local instance classicalFinDecidable (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end EntropyFinal
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryParents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*}

def descriptorActive (n : ℕ) (D : FixedDescriptor n) : Finset ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => (D i).2.2 = true).image (fun i => i.val+2)

def descriptorNode (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ℕ) : V × Bool :=
  node d x n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none)) i

def descriptorParent (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => (j<2 ∨ j ∈ descriptorActive n D) ∧
    (descriptorNode (E := E) d x n D j).2 = (descriptorNode (E := E) d x n D i).2).sup id

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype I]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Bool)

abbrev ActiveIndex (n : ℕ) (D : FixedDescriptor n) := {i : Fin n // (D i).2.2 = true}

def activeLeft (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ActiveIndex n D) : V :=
  (descriptorNode (E := E) d x n D (i.val.val+2)).1

def activeRight (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ActiveIndex n D) : V :=
  (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val.val+2))).1

noncomputable section Entropy
local instance pairsClassicalFinDecidable (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end Entropy
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinarySwitches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph SearchTree BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def switched (n : ℕ) (h : History E n) (ω : Set E) (S : Finset ℕ) : Set E :=
  {e | ω e ∨ ∃ i ∈ S, nodeMark n h i = some e}

def targets (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) : Set V :=
  {v | ∃ j < i, (node d x n h j).1=v}

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*}

noncomputable def representative (f : X → Y) (x₀ : X) (y : Y) : X :=
  if h : ∃ x, f x = y then h.choose else x₀

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryTranscript
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*}

abbrev stepLeft (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : V :=
  (descriptorNode (E := E) d x n D (i.val+2)).1
abbrev stepRight (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : V :=
  (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val+2))).1
abbrev stepTargets (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : Set V :=
  scheduledTargets (E := E) d x n (fun j => (D j).1) i.val

def activeSteps (n : ℕ) (D : FixedDescriptor n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (D i).2.2 = true

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

noncomputable def pairQuery (i : Fin n) : QueryTree E :=
  (pair G (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i)).bare

noncomputable def selectedTranscript (i : Fin n) (ω : E → Bool) : E → Bool :=
  if (D i).2.2 = true then
    representative (pairQuery G d x n D i).run (fun _ => false) ((pairQuery G d x n D i).run ω)
  else ω

noncomputable def selectedWeight (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if (D i).2.2 = true then match m with
    | none => 0
    | some e => markWeight G order (stepTargets (E := E) d x n D i)
        (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i) p w ω e
  else scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m

noncomputable def selectedCost (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if (D i).2.2 = true then match m with
    | none => 0
    | some e => markCost G order (stepTargets (E := E) d x n D i)
        (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i) p w ω e
  else 0

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryInverseCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

noncomputable section Cost
local instance inverseCostFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end Cost
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ReverseReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.ReverseReference
open scoped Classical

variable {X M : Type*} [Fintype M]

noncomputable def weight (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) :
    (n : ℕ) → X → (Fin n → M) → ℝ
  | 0, _, _ => 1
  | n+1, x, m => k n x (m (Fin.last n)) *
    weight k u n (u n x (m (Fin.last n))) (Fin.init m)

def recover (u : ℕ → X → M → X) : (n : ℕ) → X → (Fin n → M) → X
  | 0, x, _ => x
  | n+1, x, m => recover u n (u n x (m (Fin.last n))) (Fin.init m)

section Terminal
variable [Fintype X] {I : Type*} [Fintype I]

noncomputable def terminalWeight (a : I → X → M → ℝ) (x : X) (m : I → M) : ℝ :=
  ∏ i, a i x (m i)

noncomputable def joint (μ : X → ℝ) (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (a : I → X → M → ℝ) (n : ℕ) (z : X × (Fin n → M) × (I → M)) : ℝ :=
  μ z.1 * weight k u n z.1 z.2.1 * terminalWeight a (recover u n z.1 z.2.1) z.2.2

end Terminal
end CriticalPercolation.ReverseReference

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_MarkedBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.MarkedBits
open scoped Classical
open FiniteProduct ExactExposure

variable {E I : Type*}

noncomputable def opened (S : Finset I) (m : I → Option E) (ω : E → Bool) : E → Bool :=
  fun e => if ∃ i ∈ S, m i = some e then true else ω e

noncomputable def masked (S : Finset I) (m : I → Option E) : I → Option E :=
  fun i => if i ∈ S then m i else none

end CriticalPercolation.MarkedBits

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryReverseKernels
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance kernelsFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

noncomputable def pivotGuess (i : Fin n) (ω : E → Bool) (e : E) : ℝ :=
  (LazyDFS.search G order (stepLeft (E := E) d x n D i) (stepTargets (E := E) d x n D i)).reverseGuess
    p (fun σ => ∃ b ∈ stepTargets (E := E) d x n D i,
      (G.openGraph σ).Reachable (stepLeft (E := E) d x n D i) b) w (configuration ω) 0 e

noncomputable def inverseKernel (j : ℕ) (ω : E → Bool) (m : Option E) : ℝ :=
  if hj : j < n then
    if (⟨j,hj⟩ : Fin n) ∈ activeSteps n D then
      match m with | none => 0 | some e => pivotGuess G order d x p w n D ⟨j,hj⟩ ω e
    else if m = none then 1 else 0
  else if m = none then 1 else 0

noncomputable def inverseUpdate (j : ℕ) (ω : E → Bool) (m : Option E) : E → Bool :=
  if hj : j < n then
    if (⟨j,hj⟩ : Fin n) ∈ activeSteps n D then
      match m with | none => ω | some e => Function.update ω e false
    else ω
  else ω

noncomputable def contactTotal (i : Fin n) (ω : E → Bool) : ℝ :=
  ∑ m, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m

noncomputable def inactiveKernel (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if i ∈ activeSteps n D then if m=none then 1 else 0
  else if contactTotal G order d x p w n D i ω = 0 then if m=none then 1 else 0
  else scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m /
    contactTotal G order d x p w n D i ω

noncomputable def inverseReference : ((E → Bool) × (Fin n → Option E) × (Fin n → Option E)) → ℝ :=
  ReverseReference.joint (FiniteProduct.density (QueryTree.bitWeight p))
    (inverseKernel G order d x p w n D) (inverseUpdate (E := E) n D)
    (inactiveKernel G order d x p w n D) n

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryOutput
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph LazyDFS BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def HasSide (L : List (V × Bool)) (ω : Set E) (b : Bool) (v : V) : Prop :=
  ∃ z ∈ L, z.2=b ∧ (G.openGraph ω).Reachable z.1 v

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*}
local instance stagesFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

noncomputable def stageIndices (n : ℕ) (D : FixedDescriptor n) (k : ℕ) : Finset (Fin n) :=
  (activeSteps n D).filter fun i => i.val < k

noncomputable def stage (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool)
    (m : Fin n → Option E) (k : ℕ) : E → Bool := opened (stageIndices n D k) m ω

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryReversePrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance pricesFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryLikelihood
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance likelihoodFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

def inversePenalty (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  (if i ∈ activeSteps n D then (1+selectedCost G order d x p w n D i ω m)^2 else 1) *
    max 1 (contactTotal G order d x p w n D i ω)

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryReferenceLikelihood
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance refLikelihoodFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

noncomputable def recorded (n : ℕ) (D : FixedDescriptor n) (z : (E → Bool) × (Fin n → Option E)) :
    (E → Bool) × (Fin n → Option E) × (Fin n → Option E) :=
  (stage n D z.1 z.2 n,masked (activeSteps n D) z.2,masked (activeSteps n D)ᶜ z.2)

variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

def inverseLog (ω : E → Bool) (m : Fin n → Option E) : ℝ :=
  2*(∑ i ∈ activeSteps n D, Real.log (1+selectedCost G order d x p w n D i ω (m i))) +
    logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration ω)

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryOutputEntropy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
local instance outputEntropyFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

noncomputable def outputMass : (E → Bool) → ℝ :=
  pushMass (fun z => stage n D z.1 z.2 n) (conditionedMass G order d x p w s n D)

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryEventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
local instance eventBoundFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteInterpolation
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E]

local instance interpolationFinDec_r97867b_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
def allDarts (G : BondGraph V E) : List (LazyDFS.Dart V E) :=
  (Finset.univ.filter (fun a : LazyDFS.Dart V E => G.ends a.2.1 = s(a.1,a.2.2))).toList

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteInterpolationMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def twoClusterEvent (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.openGraph ω).Reachable u v} ∩ G.clusterTail u s ∩ G.clusterTail v s

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_WitnessEvents
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def witnessedTwoCluster (K : Set E) (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.openGraph ω).Reachable u v} ∩
    {ω | K∩ω ∈ G.clusterTail u s ∩ G.clusterTail v s}

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_BallIncidence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_bond_endpoints {K : Set E} (hK : K.Finite) :
    (⋃ e∈K, {v | v∈G.ends e}).Finite := by
  apply hK.biUnion
  intro e _
  convert (G.ends e).toFinset.finite_toSet using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  exact Sym2.mem_toFinset.symm

lemma finite_bonds_in_ball (hconnected : G.fullGraph.Connected) (o : V)
    {K : Set E} (hK : K.Finite) : ∃ W, K ⊆ G.inducedEdges (G.vertexBall o W) := by
  obtain ⟨W,hW⟩ := G.finite_subset_vertexBall hconnected o (G.finite_bond_endpoints hK)
  refine ⟨W,?_⟩
  intro e he v hv
  exact hW (Set.mem_iUnion₂.mpr ⟨e,he,hv⟩)

lemma inducedEdges_monotone : Monotone G.inducedEdges := by
  intro S T h e he v hv
  exact h (he v hv)

def inducedBallExhaustion (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (o : V) : Set.FiniteExhaustion (Set.univ : Set E) where
  toFun n := G.inducedEdges (G.vertexBall o n)
  finite' n := G.finite_inducedEdges hlocal (G.vertexBall_finite hlocal o n)
  subset_succ' n := G.inducedEdges_monotone (G.vertexBall_mono o (Nat.le_succ n))
  iUnion_eq' := by
    apply Set.eq_univ_of_forall
    intro e
    obtain ⟨W,hW⟩ := G.finite_bonds_in_ball hconnected o (Set.finite_singleton e)
    exact Set.mem_iUnion.mpr ⟨W,hW rfl⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

noncomputable def clusterSize (ω : Set E) (v : V) : ℕ :=
  (G.cluster ω v).toFinset.card

noncomputable def rootMass (f : ℕ → ℝ) (ω : Set E) (v : V) : ℝ :=
  f (G.clusterSize ω v) / G.clusterSize ω v

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_CappedDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

namespace BondGraph
open FiniteProduct

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

def edgeClusterMass (f : ℕ → ℝ) (ω : Set E) (e : E) : ℝ :=
  ∑ v, if e ∈ G.incidentEdges (G.cluster ω v) then G.rootMass f ω v else 0

variable [Fintype E]

def clusterDiscrepancy (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  ∑ e, if e ∈ G.incidentEdges (G.cluster ω v) then (if ω e then -(1-p)/p else 1) else 0

def edgeDiscrepancy (f : ℕ → ℝ) (p : ℝ) (ω : Set E) (e : E) : ℝ :=
  (if ω e then -(1-p)/p else 1) * G.edgeClusterMass f ω e

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_InfiniteUniquenessGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def distinctInfiniteEvent (x y : V) : Set (Set E) :=
  {ω | (G.cluster ω x).Infinite ∧ (G.cluster ω y).Infinite ∧
    ¬ (G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_InfiniteUniqueness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def atMostOneInfinite : Set (Set E) :=
  {ω | ∀ x y, (G.cluster ω x).Infinite → (G.cluster ω y).Infinite →
    (G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DirectionalTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def infiniteVertices (ω : Set E) : Set V := {v | (G.cluster ω v).Infinite}

def directionUnbounded (f : V → ℝ) : Set (Set E) :=
  {ω | ∀ n : ℕ, ∃ v, (n : ℝ)<f v ∧ v∈G.infiniteVertices ω}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteSusceptibility
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation
open FiniteProduct

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def openIncident (ω : Set E) (v : V) : Set E :=
  G.incidentEdges (G.cluster ω v) ∩ ω

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Classification_StructuredCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E Λ N : Type*} (G : BondGraph V E)
  [Group Λ] [Group N] [MulAction Λ V] [MulAction Λ E]

def integerPairComplex (z : ℤ×ℤ) : ℂ := (z.1 : ℂ)+(z.2 : ℂ)*Complex.I

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_CylinderApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def finiteCoordinateEvents : Set (Set (Set E)) :=
  {A | ∃ S : Finset E, MeasurableSet[blockSigma (S : Set E)] A}

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterNumber
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def infinitelyManyInfiniteClusters (ω : Set E) : Prop :=
  ∀ S : Finset V, ∃ v, (G.cluster ω v).Infinite ∧
    ∀ s ∈ S, ¬ (G.openGraph ω).Reachable v s

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularClusterMass
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stabilizerWeight (o x : V) : ℝ≥0∞ := ENNReal.ofReal (G.modularRatio x o)

def modularMass (o : V) (S : Set V) : ℝ≥0∞ :=
  ∑' x : V, if x∈S then G.stabilizerWeight o x else 0

@[simp] lemma stabilizerWeight_self (o : V) : G.stabilizerWeight o o = 1 := by
  simp [stabilizerWeight,modularRatio_self]

def lightInfiniteEvent (o v : V) : Set (Set E) :=
  {ω | (G.cluster ω v).Infinite ∧ G.modularMass o (G.cluster ω v) < ∞}

def heavyClusterEvent (o v : V) : Set (Set E) :=
  {ω | G.modularMass o (G.cluster ω v) = ∞}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyClusterNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def atMostOneHeavy (o : V) : Set (Set E) :=
  {ω | ∀ x y, G.modularMass o (G.cluster ω x) = ∞ →
    G.modularMass o (G.cluster ω y) = ∞ → (G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakClusters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterPeak (ω : Set E) (x : V) : Prop :=
  ∀ z, (G.openGraph ω).Reachable x z → G.stabilizerWeight x z ≤ 1

def clusterPeaks (ω : Set E) (v : V) : Set V :=
  {x | (G.openGraph ω).Reachable v x ∧ G.clusterPeak ω x}

def peakBound (N : ℕ) (ω : Set E) (v : V) : Prop :=
  ∃ S : Finset V, S.card ≤ N ∧ G.clusterPeaks ω v ⊆ S

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularSuperlevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterUpperSet (ω : Set E) (v : V) : Set V :=
  {x | x ∈ G.cluster ω v ∧ 1 ≤ G.stabilizerWeight v x}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakRatioTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def peakRatioTransport (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y∈G.clusterPeaks ω x then
    (G.modularMass y (G.cluster ω x))⁻¹ * ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹
  else 0

def clusterPeakRatio (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.peakRatioTransport ω x y

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularClusterCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def reciprocalClusterMass (ω : Set E) (x : V) : ℝ≥0∞ :=
  (G.modularMass x (G.cluster ω x))⁻¹

def finiteMassIndicator (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.modularMass x (G.cluster ω x)=∞ then 0 else 1

def incidentClusterCount (ω : Set E) (e : E) : ℝ≥0∞ :=
  ∑' x, if e∈G.incidentEdges (G.cluster ω x) then G.reciprocalClusterMass ω x else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def bondWeight (o : V) (e : E) : ℝ≥0∞ := ∑ v ∈ (G.ends e).toFinset, G.stabilizerWeight o v

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure OrbitRepresentatives where
  roots : Finset V
  cover : ∀ x : V, ∃ u ∈ roots, ∃ φ : G.Aut, φ.vertex u = x
  unique : ∀ u ∈ roots, ∀ v ∈ roots, ∀ φ : G.Aut, φ.vertex u = v → u = v

lemma finite_vertexOrbits (hq : G.QuasiTransitive) :
    Finite (MulAction.orbitRel.Quotient G.Aut V) := by
  obtain ⟨S,hS,hcover⟩ := hq
  apply Set.finite_univ_iff.mp
  apply (hS.image (fun x : V => (Quotient.mk'' x : MulAction.orbitRel.Quotient G.Aut V))).subset
  intro q _
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨u,hu,φ,hφ⟩ := hcover x
    refine ⟨u,hu,?_⟩
    apply Quotient.sound
    exact MulAction.mem_orbit_symm.mpr (MulAction.mem_orbit_iff.mpr ⟨φ,hφ⟩)

def orbitRepresentatives (hq : G.QuasiTransitive) : G.OrbitRepresentatives := by
  letI := G.finite_vertexOrbits hq
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient G.Aut V)
  let S : Finset V := Finset.univ.image (Quotient.out : MulAction.orbitRel.Quotient G.Aut V → V)
  refine ⟨S,?_,?_⟩
  · intro x
    let q : MulAction.orbitRel.Quotient G.Aut V := Quotient.mk'' x
    refine ⟨q.out,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩
    have heq : (Quotient.mk'' q.out : MulAction.orbitRel.Quotient G.Aut V) = Quotient.mk'' x := q.out_eq'
    exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp (Quotient.exact heq))
  · intro u hu v hv φ hφ
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
    have heq : (Quotient.mk'' r.out : MulAction.orbitRel.Quotient G.Aut V) = Quotient.mk'' q.out :=
      Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨φ,hφ⟩)
    rw [Quotient.out_eq',Quotient.out_eq'] at heq
    exact congrArg Quotient.out heq.symm

abbrev PairOrbit := MulAction.orbitRel.Quotient G.Aut (V × V)

def pairOrbit (x y : V) : G.PairOrbit := Quotient.mk'' (x,y)

lemma pairOrbit_eq {x y u v : V} : G.pairOrbit x y = G.pairOrbit u v ↔
    ∃ φ : G.Aut, φ.vertex x = u ∧ φ.vertex y = v := by
  constructor
  · intro h
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
    exact ⟨φ,congrArg Prod.fst hφ,congrArg Prod.snd hφ⟩
  · rintro ⟨φ,hx,hy⟩
    apply Eq.symm
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext hx hy⟩

lemma Aut.pairOrbit (φ : G.Aut) (x y : V) :
    G.pairOrbit (φ.vertex x) (φ.vertex y) = G.pairOrbit x y :=
  (G.pairOrbit_eq.mpr ⟨φ,rfl,rfl⟩).symm

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

abbrev RootedPair := {x // x ∈ R.roots} × V

def pairMap (p : R.RootedPair) : G.PairOrbit := G.pairOrbit p.1 p.2

lemma fiber_root_eq (x : {x // x∈R.roots}) (y : V)
    (p : (pairMap G R) ⁻¹' {G.pairOrbit x y}) : p.val.1 = x := by
  have hh : G.pairOrbit (x:V) y = G.pairOrbit (p.val.1:V) p.val.2 := p.property.symm
  obtain ⟨φ,hφ,_⟩ := G.pairOrbit_eq.mp hh
  exact Subtype.ext (R.unique x x.property p.val.1 p.val.1.property φ hφ).symm

lemma fiber_snd_mem (x : {x // x∈R.roots}) (y : V)
    (p : (pairMap G R) ⁻¹' {G.pairOrbit x y}) : p.val.2 ∈ G.stabilizerOrbit x y := by
  have hh : G.pairOrbit (x:V) y = G.pairOrbit (p.val.1:V) p.val.2 := p.property.symm
  obtain ⟨φ,hφ,hy⟩ := G.pairOrbit_eq.mp hh
  exact G.mem_stabilizerOrbit.mpr ⟨φ,by rw [hφ,fiber_root_eq G R x y p],hy⟩

def fiberEquiv (x : {x // x∈R.roots}) (y : V) :
    (pairMap G R) ⁻¹' {G.pairOrbit x y} ≃ G.stabilizerOrbit x y where
  toFun p := ⟨p.val.2,fiber_snd_mem G R x y p⟩
  invFun z := ⟨(x,z),by
    obtain ⟨φ,hx,hz⟩ := G.mem_stabilizerOrbit.mp z.property
    exact (G.pairOrbit_eq.mpr ⟨φ,hx,hz⟩).symm⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (fiber_root_eq G R x y p).symm rfl
  right_inv z := rfl

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_OrbitalMassTransport
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def swapPairOrbitFn : G.PairOrbit → G.PairOrbit :=
  Quotient.map Prod.swap (by
    intro a b hab
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp hab
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext (congrArg Prod.snd hφ) (congrArg Prod.fst hφ)⟩)

def swapPairOrbit : G.PairOrbit ≃ G.PairOrbit where
  toFun := swapPairOrbitFn G
  invFun := swapPairOrbitFn G
  left_inv q := by induction q using Quotient.inductionOn' with | h p => rfl
  right_inv q := by induction q using Quotient.inductionOn' with | h p => rfl

@[simp] lemma swapPairOrbit_mk (x y : V) :
    G.swapPairOrbit (G.pairOrbit x y) = G.pairOrbit y x := rfl

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

def weightedRow (w : V → ℝ) (F : V → V → ℝ) (p : R.RootedPair) : ℝ :=
  w p.1 * F p.1 p.2

lemma weightedRow_finite (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ x, (Function.support (F x)).Finite) :
    (Function.support (weightedRow G R w F)).Finite := by
  apply (Set.finite_iUnion (fun x : {x // x∈R.roots} =>
    (hF x).image (Prod.mk x))).subset
  intro p hp
  refine Set.mem_iUnion.mpr ⟨p.1,p.2,?_,rfl⟩
  intro hz
  exact hp (by simp only [weightedRow,hz,mul_zero])

lemma fiber_sum_root (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x : {x // x∈R.roots}) (y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, weightedRow G R w F p) =
      w x * (G.suborbitCard x y : ℝ) * F x y := by
  let := (G.stabilizerOrbit_finite hc hl x y).fintype
  rw [← (fiberEquiv G R x y).symm.tsum_eq]
  have hv (z : G.stabilizerOrbit x y) :
      weightedRow G R w F ((fiberEquiv G R x y).symm z) = w x * F x y := by
    change w x * F x z = w x * F x y
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp z.property
    have hh := hF φ x y
    rw [hx,hy] at hh
    rw [hh]
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (G.stabilizerOrbit x y) = G.suborbitCard x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]
  ring

lemma fiber_sum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (hw : ∀ (φ : G.Aut) x, w (φ.vertex x) = w x)
    (F : V → V → ℝ) (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, weightedRow G R w F p) =
      w x * (G.suborbitCard x y : ℝ) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ.vertex.symm y
  have hy : φ.vertex v = y := φ.vertex.apply_symm_apply y
  have hq : G.pairOrbit (φ.vertex u) y = G.pairOrbit u v := by
    rw [←hy,Aut.pairOrbit]
  rw [hq,fiber_sum_root G R hc hl w F hF ⟨u,hu⟩ v]
  change w u * (G.suborbitCard u v : ℝ) * F u v = _
  rw [←hy,hw,Aut.suborbitCard,hF]

lemma tsum_weightedRow (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ x, (Function.support (F x)).Finite) :
    (∑' p, weightedRow G R w F p) = ∑ x ∈ R.roots, w x * ∑' y, F x y := by
  have hs : Summable (weightedRow G R w F) := summable_of_hasFiniteSupport (weightedRow_finite G R w F hF)
  rw [hs.tsum_prod]
  simp only [weightedRow,tsum_mul_left,tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => w x * ∑' y, F x y)

lemma massTransport (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (hw : ∀ (φ : G.Aut) x, w (φ.vertex x) = w x)
    (hbal : ∀ x y, w x * (G.suborbitCard x y : ℝ) = w y * (G.suborbitCard y x : ℝ))
    (F : V → V → ℝ) (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (hrow : ∀ x, (Function.support (F x)).Finite)
    (hcol : ∀ y, (Function.support (fun x => F x y)).Finite) :
    (∑ x ∈ R.roots, w x * ∑' y, F x y) = ∑ y ∈ R.roots, w y * ∑' x, F x y := by
  let F' := fun x y => F y x
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := hF φ y x
  have hs : Summable (weightedRow G R w F) := summable_of_hasFiniteSupport (weightedRow_finite G R w F hrow)
  have ht : Summable (weightedRow G R w F') := summable_of_hasFiniteSupport (weightedRow_finite G R w F' hcol)
  rw [←tsum_weightedRow G R w F hrow,←tsum_weightedRow G R w F' hcol]
  calc
    _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q}, weightedRow G R w F p :=
      (hs.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq.symm
    _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          weightedRow G R w F' p := by
      apply tsum_congr
      intro q
      induction q using Quotient.inductionOn' with
      | h p =>
        change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2}, weightedRow G R w F z) =
          ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1}, weightedRow G R w F' z
        rw [fiber_sum G R hc hl w hw F hF,fiber_sum G R hc hl w hw F' hF',hbal]
    _ = ∑' p, weightedRow G R w F' p := by
      exact (G.swapPairOrbit.tsum_eq (fun q =>
        ∑' p : (pairMap G R) ⁻¹' {q}, weightedRow G R w F' p)).trans
          (ht.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_TiltedTransportENNReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

def ennRow (F : V → V → ℝ≥0∞) (p : R.RootedPair) : ℝ≥0∞ := F p.1 p.2

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_NormalizedIncidenceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def normalizedSelectedIncidence (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  (∑' e, if e∈G.incidentEdges (G.cluster ω x) then H ω e*G.bondWeight x e else 0)*
    G.reciprocalClusterMass ω x

def normalizedIncidenceTransport (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  ∑' e, if e∈G.incidentEdges (G.cluster ω x) ∧ y∈G.ends e then
    H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ExpectedIncidenceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def selectedIncidenceReturn (hl : G.LocallyFinite) (H : Set E → E → ℝ≥0∞)
    (ω : Set E) (y : V) : ℝ≥0∞ :=
  ∑ e∈(hl y).toFinset, H ω e*G.incidentClusterCount ω e

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyPeaks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def heavyPeakTransport (N : ℕ) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if G.modularMass x (G.cluster ω x) = ∞ ∧ G.peakBound N ω x ∧ y∈G.clusterPeaks ω x then 1 else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def peakReturn (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.clusterPeak ω x then ((G.clusterPeaks ω x).encard : ℝ≥0∞)⁻¹ else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedPeakTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def normalizedClusterVolume (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.clusterPeakRatio ω x=0 then 0 else (G.clusterPeakRatio ω x)⁻¹

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakVolumeBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def peakVolumeBand (T U : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U then
    G.peakReturn ω x else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def centeredCoefficient (p : ℝ) (ω : Set E) (e : E) : ℝ := if e∈ω then 1-p else -p

def weightedIncidenceTerm (p : ℝ) (ω : Set E) (x : V) (e : E) : ℝ :=
  if e∈G.incidentEdges (G.cluster ω x) then
    (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0

def weightedDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  ∑' e, G.weightedIncidenceTerm p ω x e

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_NormalizedDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def normalizedAbsoluteDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ENNReal.ofReal |G.weightedDiscrepancy p ω x| / G.modularMass x (G.cluster ω x)

def discrepancyVolumeBand (p : ℝ) (T U : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U then
    G.normalizedAbsoluteDiscrepancy p ω x else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedDiscrepancyLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def restrictedWeightedTerm (s : Set E) (p : ℝ) (ω : Set E) (x : V) (e : E) : ℝ :=
  if e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x) then
    (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0

def restrictedWeightedDiscrepancy (s : Set E) (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  ∑' e, G.restrictedWeightedTerm s p ω x e

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_DiscrepancyTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators Topology

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

def discrepancyVolumeTail (p : ℝ) (T : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x then G.normalizedAbsoluteDiscrepancy p ω x else 0

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_MonotoneBernoulli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct

variable {E : Type*}

def markLaw : Measure (E → ℝ) := Measure.infinitePi (fun _ : E => Priority.uniform01)

instance instIsProbabilityMeasureForallRealMarkLaw : IsProbabilityMeasure (markLaw (E := E)) := by
  unfold markLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def atParameter (p : unitInterval) (u : E → ℝ) : Set E := {e | u e < p}

def reindexMarks (e : E ≃ E) (u : E → ℝ) : E → ℝ := fun x => u (e.symm x)

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def heavyFlag (p : unitInterval) (u : E → ℝ) (x : V) : Prop :=
  G.modularMass x (G.cluster (atParameter p u) x) = ∞

def heavyRestrictedPeakTransport (p q : unitInterval) (u : E → ℝ) (x y : V) : ℝ≥0∞ :=
  if G.heavyFlag p u x then G.peakRatioTransport (atParameter q u) x y else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_SignedDiscrepancyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def normalizedSignedDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  G.weightedDiscrepancy p ω x / (G.modularMass x (G.cluster ω x)).toReal

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_CriticalHeavyIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterCountDrop (ω : Set E) (e : E) : ℝ :=
  (G.incidentClusterCount (ω\{e}) e).toReal -
    (G.incidentClusterCount (insert e ω) e).toReal

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ForcedDisconnectContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def forcedClosedSeparated (ω : Set E) (e : E) : Prop :=
  ∃ a∈G.ends e, ∃ b∈G.ends e, ¬(G.openGraph (ω\{e})).Reachable a b

def disconnectedIndicator (ω : Set E) (e : E) : ℝ :=
  if G.forcedClosedSeparated ω e then 1 else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BandScale
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterBand (o : V) (s : ℕ) : Set (Set E) :=
  G.clusterTail o s \ G.clusterTail o (s ^ 2)

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_SuperpolynomialRadius
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def SuperpolynomialGrowth : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n≥N, ∀ v : V, n^M≤(G.vertexBall v n).ncard

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_GrowthAlternatives
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def maxVolume (n : ℕ) : ℕ := sSup (Set.range fun v => (G.vertexBall v n).ncard)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ContractingDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def safeBallDomain (o : V) (T : ℝ) (R : ℕ) : Set V :=
  {x | ∃ z, x∈G.vertexBall z R ∧
    ∀ y∈G.vertexBall z R, G.modularRatio y o≤T}

def InsideWalk (S : Set V) (x y : V) (n : ℕ) : Prop :=
  ∃ p : G.fullGraph.Walk x y, p.length≤n ∧ ∀ v∈p.support, v∈S

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyHarris
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def massTailEvent (o v : V) (a : ℝ≥0∞) : Set (Set E) :=
  {ω | a<G.modularMass o (G.cluster ω v)}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DescendingFan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def weightCeiling (v : V) (K : ℝ≥0∞) : Set V := {x | G.stabilizerWeight v x≤K}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_InvariantFiniteSets
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def vertexSetBound (_G : BondGraph V E) (A : Set E → Set V) (N : ℕ) (ω : Set E) : Prop :=
  ∃ S : Finset V, S.card≤N ∧ A ω ⊆ S

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyFiniteGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def distinctHeavyEvent (o x y : V) : Set (Set E) :=
  {ω | G.modularMass o (G.cluster ω x)=∞ ∧ G.modularMass o (G.cluster ω y)=∞ ∧
    ¬(G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SliceExploration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal symmDiff Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def freshClusterBoundary (X : Set E) (v : V) (ω : Set E) : Set E :=
  G.cutEdges (G.cluster (ω∩X) v) \ X

def smallFreshBoundary (X : Set E) (v : V) (M : ℕ) : Set (Set E) :=
  {ω | (G.cluster (ω∩X) v).Finite ∧ (G.freshClusterBoundary X v ω).ncard ≤ M}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_OpenFrontierDivergence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def fewOpenFreshBoundary (X : Set E) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | (G.cluster (ω∩X) v).Finite ∧ (G.freshClusterBoundary X v ω ∩ ω).ncard ≤ N}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_FreshExitWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def freshExitEvent (S : Set V) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | ∃ F : Finset E, N≤F.card ∧
    (F : Set E)⊆G.freshClusterBoundary (G.inducedEdges S) v ω∩ω}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_DomainFreshExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def domainFreshExitEvent (D S : Set V) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | ω∩G.inducedEdges D ∈ G.freshExitEvent S v N}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_LightSliceFrontier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def modularUpperSlice (o : V) (ε : ℝ) : Set V := {x | ε ≤ G.modularRatio x o}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_NestedLayerBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def boundedDomainFreshExitEvent (D S : Set V) (v : V) (N : ℕ) (M : ℝ≥0∞) : Set (Set E) :=
  G.domainFreshExitEvent D S v N ∩
    {ω | G.modularMass v (G.cluster ((ω∩G.inducedEdges D)∩G.inducedEdges S) v)≤M}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_LayerExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def entrySeeds (D : Set V) (o : V) (ω : Set E) : Set V :=
  G.cluster (ω∩(G.inducedEdges D)ᶜ) o ∩ D

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_LayerCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def layerComponent (D H : Set V) (ω : Set E) (x : V) : Set V :=
  G.cluster ((ω∩G.inducedEdges D)∩G.inducedEdges Hᶜ) x

def openLayerExits (D H : Set V) (ω : Set E) (x : V) : Set E :=
  G.freshClusterBoundary (G.inducedEdges Hᶜ) x (ω∩G.inducedEdges D)∩(ω∩G.inducedEdges D)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_BallCutGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ballCut (o : V) (n : ℕ) : Set E := G.cutEdges (G.vertexBall o n)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_DeletedTailGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation
namespace BondGraph
open ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

def exitEndpoint (U : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ U then (G.ends e).out.2 else (G.ends e).out.1

def exitVertices (U : Set V) : Finset V :=
  (G.incidentEdges U).toFinset.image (G.exitEndpoint U)

def smallDamage (H : SimpleGraph V) (U : Set V) (s : ℕ) : Finset V :=
  U.toFinset ∪ ((G.exitVertices U).filter
    (fun w => (component (delete H U) w).toFinset.card < s)).biUnion
      (fun w => (component (delete H U) w).toFinset)

def tailCount (H : SimpleGraph V) (B : Finset V) (s : ℕ) : ℝ :=
  ∑ v∈B, if s≤(component H v).toFinset.card then 1 else 0

def exteriorTailCount (H : SimpleGraph V) (U : Set V) (B : Finset V) (s : ℕ) : ℝ :=
  ∑ v∈B, if v∉U ∧ s≤(component (delete H U) v).toFinset.card then 1 else 0

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_UnimodularGeometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def CombinatoriallyUnimodular.unimodularRoot (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) : G.UnimodularRoot := by
  let R := G.orbitRepresentatives hq
  let Z := ∑ x ∈ R.roots, G.modularRatio o x
  have hZ : 0 < Z := by
    obtain ⟨u,hu,_,_⟩ := R.cover o
    exact Finset.sum_pos' (fun x _ => (G.modularRatio_pos hc hl o x).le)
      ⟨u,hu,G.modularRatio_pos hc hl o u⟩
  let w := fun x => G.modularRatio o x / Z
  have hw (φ : G.Aut) (x : V) : w (φ.vertex x) = w x := by
    simp only [w,CombinatoriallyUnimodular.rootWeight_invariant G hu hc hl]
  have hbal (x y : V) : w x * (G.suborbitCard x y : ℝ) = w y * (G.suborbitCard y x : ℝ) := by
    simp only [w,div_mul_eq_mul_div]
    rw [G.modularRatio_card_balance hc hl]
  refine ⟨R.roots,w,?_,?_,R.cover,?_⟩
  · intro x _
    exact div_pos (G.modularRatio_pos hc hl o x) hZ
  · change (∑ x ∈ R.roots, G.modularRatio o x / Z) = 1
    rw [←Finset.sum_div,div_self (ne_of_gt hZ)]
  · exact OrbitRepresentatives.massTransport G R hc hl w hw hbal

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_MainResidualBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def twoHeavyDistinctEvent (o x y : V) : Set (Set E) :=
  G.heavyClusterEvent o x ∩ G.heavyClusterEvent o y ∩
    {ω | ¬ (G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EncounterGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def separatedInfiniteTupleEvent {k : ℕ} (v : Fin k → V) : Set (Set E) :=
  {ω | (∀ i, (G.cluster ω (v i)).Infinite) ∧
    Pairwise (fun i j => ¬(G.openGraph ω).Reachable (v i) (v j))}

def encounterEvent (J : Set E) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | ∃ v : Fin k → V, (∀ i, (G.openGraph ω).Reachable o (v i)) ∧
    (∀ i, (G.cluster (ω\J) (v i)).Infinite) ∧
    Pairwise (fun i j => ¬(G.openGraph (ω\J)).Reachable (v i) (v j))}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FullOrbitalStructureTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def fullOrbitalQuotientHom (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal] :
    Λ →* (G.orbitPower o L ≃g G.orbitPower o L) ⧸ H :=
  (QuotientGroup.mk' H).comp ((G.orbitPowerHom o L).comp Λ.subtype)

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_LayerExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def seedExpectation (q : unitInterval) (D : Set V) (o : V) : ℝ≥0∞ :=
  ∑' x, G.law q {ω | x∈G.entrySeeds D o ω}

def goodEntrySeeds (D H : Set V) (o : V) (N M : ℕ) (ω : Set E) : Set V :=
  G.entrySeeds D o ω ∩ {x | x∉H ∧ ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M}

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_LightClusterNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def lightInfinitePeaks (ω : Set E) : Set V :=
  {v | ω∈G.lightInfiniteEvent v v ∧ G.clusterPeak ω v}

def lightClusterCover (ω : Set E) (S : Set V) : Prop :=
  ∀ v, ω∈G.lightInfiniteEvent v v → ∃ s∈S, (G.openGraph ω).Reachable v s

def infinitelyManyLightClusters (ω : Set E) : Prop :=
  ∀ S : Finset V, ∃ v, ω∈G.lightInfiniteEvent v v ∧
    ∀ s∈S, ¬(G.openGraph ω).Reachable v s

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_LightTwoPointDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def upperEscapeEvent (v : V) (R : ℕ) : Set (Set E) :=
  {ω | ∃ x, x∈G.clusterUpperSet ω v ∧ x∉G.vertexBall v R}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphQuotientPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation
namespace CompactQuotient

def HasSparsePolynomialWordGrowth (A : Type*) [Group A] : Prop :=
  ∃ S : Set A, S.Finite ∧ (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∃ d : ℕ, ∀ R : ℕ, ∃ n≥R, (S^n).ncard≤n^d

end CompactQuotient
end CriticalPercolation
end
end

end OAI
end


